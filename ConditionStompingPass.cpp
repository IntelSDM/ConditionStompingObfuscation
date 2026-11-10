#include "ConditionStompingPass.h"

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <cstdint>
#include <cstdlib>
#include <vector>

using namespace llvm;

struct ARXConfig
{
    uint64_t HashSalt;
    unsigned HashVal1;
    unsigned HashVal2;
    uint64_t KDFSalt;
    unsigned KDFVal1;
    unsigned KDFVal2;
};

static ARXConfig ARX =
{
    0xA5A5A5A5A5A5A5A5ULL, 11, 53,
    0xC5C5C5C5C5C5C5C5ULL, 13, 51
};


static void ARXInit()
{
    auto rand64 = []() -> uint64_t
    {
        return (((uint64_t)rand()) << 32) ^ (uint64_t)rand();
    };
    ARX.HashSalt = rand64();
    ARX.HashVal1 = 1u + (unsigned)(rand() % 63);
    ARX.HashVal2 = 64u - ARX.HashVal1;
    ARX.KDFSalt = rand64();
    ARX.KDFVal1 = 1u + (unsigned)(rand() % 63);
    ARX.KDFVal2 = 64u - ARX.KDFVal1;
}

// 5 round encrypt (add k → rol val1 → xor k → add k → ror val2); val1+val2 MUST sum to 64
static uint64_t CompileARX(uint64_t v, uint64_t k, unsigned val1, unsigned val2)
{
    v = v + k;
    v = (v << val1) | (v >> (64 - val1));
    v = v ^ k;
    v = v + k;
    v = (v << (64 - val2)) | (v >> val2);
    return v;
}

llvm::cl::opt<bool> CondStompEnable("obfcondstomp", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static constexpr unsigned MinRegion = 2;
static constexpr bool SkipLoops = false;
static constexpr bool ForceInline = true;
static constexpr unsigned MaxInlineDepth = 4;
static constexpr unsigned MaxCalleeBlocks = 100;
static constexpr unsigned MaxRegionForInline = 1500;
static constexpr unsigned MaxFixpointRounds = 3;
static constexpr bool Compound = true;
static constexpr unsigned MaxCompoundLeaves = 8;
static constexpr bool EncStringsInRegion = true;
static constexpr bool IndirectCalls = true;
static constexpr bool IndirectJumps = true;
static constexpr bool EncPointers = true;

static bool HasAnnotation(Function& f, StringRef tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getInitializer());
    if (!ca) return false;
    for (unsigned i = 0, e = ca->getNumOperands(); i < e; ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* gv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!gv || !gv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataArray>(gv->getInitializer());
        if (!cds || !cds->isCString()) continue;
        if (cds->getAsCString() == tag) return true;
    }
    return false;
}

struct Site
{
    Instruction* Term;
    CmpInst* Cmp;
    Value* V;
    uint64_t CBits;
    unsigned BitWidth;
    bool IsFP = false;
    bool IsString = false;
    bool IsCompound = false;
    Value* StringHashK = nullptr;
    unsigned GateSuccIdx;
    BasicBlock* PreSplitTrueBB;
    BasicBlock* TrueBB;
    unsigned PreSplitPredCount = 0;
};

// Function::size() walks the block list O(N); with leaf callees evaluated hundreds of times per inline iteration that walk dominates, so we memoize per module and clear at the top of RunConditionStomping
static DenseMap<Function*, unsigned> CalleeBlockCache;

static unsigned CalleeBlockCount(Function* f)
{
    auto it = CalleeBlockCache.find(f);
    if (it != CalleeBlockCache.end()) return it->second;
    unsigned n = f->size();
    CalleeBlockCache[f] = n;
    return n;
}

static unsigned CountPreds(BasicBlock* bb)
{
    unsigned n = 0;
    for (BasicBlock* p : predecessors(bb)) { (void)p; ++n; }
    return n;
}

static void MarkStomped(Instruction* i)
{
    if (!i) return;
    LLVMContext& c = i->getContext();
    if (i->getMetadata("cond_stomp.processed")) return;
    MDNode* mark = MDNode::get(c, {MDString::get(c, "stomped")});
    i->setMetadata("cond_stomp.processed", mark);
}

static bool IsStomped(const Instruction* i)
{
    return i && i->getMetadata("cond_stomp.processed") != nullptr;
}

// recursion depth is bounded by the AND tree depth (log of leaf count in practice); the maxleaves bound stops a pathologically wide tree from stalling the walker
static bool CollectAndLeaves(Value* root, std::vector<ICmpInst*>& out, unsigned maxleaves)
{
    if (auto* bin = dyn_cast<BinaryOperator>(root))
    {
        if (bin->getOpcode() == Instruction::And)
        {
            if (!CollectAndLeaves(bin->getOperand(0), out, maxleaves)) return false;
            if (out.size() > maxleaves) return false;
            if (!CollectAndLeaves(bin->getOperand(1), out, maxleaves)) return false;
            return true;
        }
    }
    if (auto* c = dyn_cast<ICmpInst>(root))
    {
        if (out.size() >= maxleaves) return false;
        if (c->getPredicate() != CmpInst::ICMP_EQ) return false;
        Value* lhs = c->getOperand(0);
        Value* rhs = c->getOperand(1);
        if (!isa<ConstantInt>(lhs) && !isa<ConstantInt>(rhs)) return false;
        Value* v = isa<ConstantInt>(rhs) ? lhs : rhs;
        if (!v->getType()->isIntegerTy()) return false;
        unsigned bw = v->getType()->getIntegerBitWidth();
        if (bw < 8 || bw > 64) return false;
        out.push_back(c);
        return true;
    }
    return false;
}

static bool TryDetectCompoundSite(BranchInst* br, std::vector<Site>& out)
{
    if (!Compound) return false;
    if (IsStomped(br)) return false;

    Value* cond = br->getCondition();
    auto* andi = dyn_cast<BinaryOperator>(cond);
    if (!andi || andi->getOpcode() != Instruction::And) return false;
    if (IsStomped(andi)) return false;

    std::vector<ICmpInst*> leaves;
    if (!CollectAndLeaves(andi, leaves, MaxCompoundLeaves) || leaves.size() < 2 || leaves.size() > MaxCompoundLeaves) return false;

    // an inner icmp a previous rewrite already stomped no longer has the plain equality shape downstream expects; reject the whole compound rather than key off a mutated leaf
    for (ICmpInst* c : leaves)
        if (IsStomped(c)) return false;

    ICmpInst* primary = leaves[0];
    Value* lhs = primary->getOperand(0);
    Value* rhs = primary->getOperand(1);
    ConstantInt* ci = dyn_cast<ConstantInt>(rhs);
    Value* v = lhs;
    if (!ci) { ci = dyn_cast<ConstantInt>(lhs); v = rhs; }
    if (!ci) return false;

    Site s;
    s.Term = br;
    s.Cmp = nullptr;
    s.V = v;
    s.CBits = ci->getZExtValue();
    s.BitWidth = ci->getBitWidth();
    s.IsFP = false;
    s.IsString = false;
    s.IsCompound = true;
    s.GateSuccIdx = 0;
    s.PreSplitTrueBB = br->getSuccessor(0);
    s.TrueBB = nullptr;
    s.PreSplitPredCount = CountPreds(s.PreSplitTrueBB);
    out.push_back(s);
    return true;
}

static void MarkSiteProcessed(const Site& s)
{
    if (s.IsCompound)
    {
        if (auto* br = dyn_cast<BranchInst>(s.Term))
            if (auto* condi = dyn_cast<Instruction>(br->getCondition()))
                MarkStomped(condi);
        return;
    }
    if (auto* sw = dyn_cast<SwitchInst>(s.Term))
    {
        (void)sw;
        // switch cases each get their own split block, so the per case marker sits on the split block's own terminator rather than on the shared switch instruction
        if (s.TrueBB && s.TrueBB->getTerminator())
            MarkStomped(s.TrueBB->getTerminator());
        return;
    }
    if (auto* br = dyn_cast<BranchInst>(s.Term))
        if (auto* condi = dyn_cast<Instruction>(br->getCondition()))
            MarkStomped(condi);
}

static bool EncryptGatedStringsInRegion(Function& f, const Site& s, ArrayRef<BasicBlock*> region, Value* k, uint64_t kct)
{
    if (!EncStringsInRegion) return false;
    if (region.empty() || !s.TrueBB) return false;
    if (!k) return false;

    struct StrEnt { GlobalVariable* Gv; };
    DenseSet<GlobalVariable*> seen;
    std::vector<StrEnt> entries;

    for (BasicBlock* bb : region)
    {
        for (Instruction& i : *bb)
        {
            for (unsigned oi = 0, oe = i.getNumOperands(); oi != oe; ++oi)
            {
                Value* op = i.getOperand(oi);
                Value* stripped = op;
                while (auto* gep = dyn_cast<GEPOperator>(stripped))
                    stripped = gep->getPointerOperand();

                auto* gv = dyn_cast<GlobalVariable>(stripped);
                if (!gv || !gv->isConstant() || !gv->hasInitializer()) continue;
                auto* arrt = dyn_cast<ArrayType>(gv->getValueType());
                if (!arrt) continue;
                Type* elemt = arrt->getElementType();
                if (!elemt->isIntegerTy(8) && !elemt->isIntegerTy(16)) continue;
                auto* init = dyn_cast<ConstantDataSequential>(gv->getInitializer());
                if (!init) continue;
                if (!seen.insert(gv).second) continue;
                entries.push_back({gv});
            }
        }
    }

    if (entries.empty()) return false;

    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);

    DenseSet<BasicBlock*> inregion(region.begin(), region.end());
    bool anychange = false;

    for (const StrEnt& e : entries)
    {
        GlobalVariable* gv = e.Gv;
        auto* init = cast<ConstantDataSequential>(gv->getInitializer());
        auto* arrt = cast<ArrayType>(gv->getValueType());
        unsigned ebits = arrt->getElementType()->getIntegerBitWidth();
        unsigned esize = ebits / 8;
        unsigned nelems = init->getNumElements();
        unsigned total = nelems * esize;
        unsigned padded = ((total + 7) / 8) * 8;
        unsigned nchunks = padded / 8;
        unsigned elemsperchunk = 8 / esize;

        // alloca sized as i64 chunks so our chunk store loop can never overrun into adjacent stack; with opaque pointers the alloca is `ptr` and matches every GV pointer use slot regardless of the original array type
        IRBuilder<> be(&f.getEntryBlock(), f.getEntryBlock().begin());
        AllocaInst* slot = be.CreateAlloca(i64, ConstantInt::get(i64, nchunks), "StrBuf");

        IRBuilder<> bs(s.TrueBB->getTerminator());

        for (unsigned chunkidx = 0; chunkidx < nchunks; ++chunkidx)
        {
            uint64_t plain = 0;
            for (unsigned kk = 0; kk < elemsperchunk; ++kk)
            {
                unsigned elemidx = chunkidx * elemsperchunk + kk;
                if (elemidx >= nelems) break;
                uint64_t v = init->getElementAsInteger(elemidx);
                plain |= v << (kk * ebits);
            }

            const uint64_t cipherct = plain ^ kct;
            Value* cipherc = ConstantInt::get(i64, cipherct);
            Value* dec = bs.CreateXor(cipherc, k, "StrDec");
            Value* dst = bs.CreateGEP(i64, slot, ConstantInt::get(i64, chunkidx), "StrDst");
            bs.CreateStore(dec, dst);
        }

        //  only direct Instruction operand uses can be swapped; a ConstantExpr use can't take an alloca as its base, so we leave it alone and let the plaintext path through that CE die naturally once all its instruction users are gone
        std::vector<Use*> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            BasicBlock* userbb = useri->getParent();
            if (!userbb) continue;
            if (!inregion.count(userbb)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(slot);

        anychange = true;
    }

    return anychange;
}

// per site 64 bit mask is deterministic across builds so a rebuild of the same bitcode produces identical binaries
static uint64_t NextCondStompMask()
{
    static uint64_t state = 0x243F6A8885A308D3ULL;
    state += 0x9E3779B97F4A7C15ULL;
    uint64_t x = state;
    x ^= x >> 30; x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 27; x *= 0x94D049BB133111EBULL;
    x ^= x >> 31;
    return x | 1;
}

// iterate CallBase not CallInst in C++ with exceptions, callees that can throw compile as invokes, and restricting to CallInst leaves direct `call sub_XXX` alongside our transformed indirect jumps in the same block setCalledOperand works on CallBase so the rewrite is identical for both
static bool IndirectCallsInRegion(Function& f, ArrayRef<BasicBlock*> region, Value* k, uint64_t kct)
{
    if (!IndirectCalls) return false;
    if (!k) return false;

    Module* m = f.getParent();
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* ptrt = PointerType::get(c, 0);

    std::vector<CallBase*> toindirect;
    for (BasicBlock* bb : region)
    {
        for (Instruction& i : *bb)
        {
            auto* call = dyn_cast<CallBase>(&i);
            if (!call) continue;
            if (isa<CallBrInst>(call)) continue;
            if (call->isInlineAsm()) continue;
            if (auto* ci = dyn_cast<CallInst>(call))
                if (ci->isMustTailCall()) continue;
            Function* callee = call->getCalledFunction();
            if (!callee) continue;
            if (callee->isIntrinsic()) continue;
            if (callee->isVarArg()) continue;
            if (callee->getName().starts_with("__cond_stomp_")) continue;
            if (HasAnnotation(*callee, "noobfus")) continue;
            toindirect.push_back(call);
        }
    }

    for (CallBase* call : toindirect)
    {
        Function* callee = call->getCalledFunction();
        uint64_t mask = NextCondStompMask();
        Constant* addr = ConstantExpr::getPtrToInt(callee, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);

        // holder is mutable so no fold through load collapses the xor chain at compile time; private linkage keeps the symbol internal
        auto* gv = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__cond_stomp_ind_call");
        gv->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

        Constant* combined = ConstantInt::get(i64, mask ^ kct);

        IRBuilder<> b(call);
        Value* loaded = b.CreateLoad(i64, gv, "CeeLoad");
        Value* effmask = b.CreateXor(combined, k, "CeeEMask");
        Value* dec = b.CreateSub(loaded, effmask, "CeeDec");
        Value* fn = b.CreateIntToPtr(dec, ptrt, "CeeP");
        call->setCalledOperand(fn);
    }

    return !toindirect.empty();
}

static bool IndirectBranchesInRegion(Function& f, const Site& s, ArrayRef<BasicBlock*> region, Value* k, uint64_t kct)
{
    if (!IndirectJumps) return false;
    if (!k) return false;

    Module* m = f.getParent();
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* ptrt = PointerType::get(c, 0);

    Instruction* splitterm = s.TrueBB ? s.TrueBB->getTerminator() : nullptr;

    std::vector<BranchInst*> toindirect;
    DenseMap<BasicBlock*, unsigned> tgtidx;
    std::vector<BasicBlock*> tgtordered;

    for (BasicBlock* bb : region)
    {
        auto* br = dyn_cast<BranchInst>(bb->getTerminator());
        if (!br) continue;
        if (br == splitterm) continue;
        bool hasehsucc = false;
        for (BasicBlock* succ : br->successors())
            if (succ && succ->isEHPad()) { hasehsucc = true; break; }
        if (hasehsucc) continue;
        toindirect.push_back(br);
        for (BasicBlock* succ : br->successors())
        {
            if (tgtidx.insert({succ, (unsigned)tgtordered.size()}).second)
                tgtordered.push_back(succ);
        }
    }
    if (toindirect.empty()) return false;

    unsigned n = tgtordered.size();
    ArrayType* arrtype = ArrayType::get(i64, n);
    SmallVector<Constant*, 32> addrentries(n);
    SmallVector<Constant*, 32> maskentries(n);
   
    SmallVector<Constant*, 32> combinedentries(n);
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t mask = NextCondStompMask();
        Constant* ba = BlockAddress::get(&f, tgtordered[i]);
        Constant* baint = ConstantExpr::getPtrToInt(ba, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        addrentries[i] = ConstantExpr::getAdd(baint, maskc);
        maskentries[i] = maskc;
        combinedentries[i] = ConstantInt::get(i64, mask ^ kct);
    }
    auto* addrtable = new GlobalVariable(*m, arrtype, false, GlobalValue::PrivateLinkage, ConstantArray::get(arrtype, addrentries), "__cond_stomp_ind_br_addrtbl");
    addrtable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    auto* combinedtable = new GlobalVariable(*m, arrtype, false, GlobalValue::PrivateLinkage, ConstantArray::get(arrtype, combinedentries), "__cond_stomp_ind_br_combined");
    combinedtable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

    Constant* zero32 = ConstantInt::get(i32, 0);
    for (BranchInst* br : toindirect)
    {
        IRBuilder<> b(br);
        Value* idx;
        if (br->isConditional())
        {
            Constant* idxt = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
            Constant* idxf = ConstantInt::get(i32, tgtidx[br->getSuccessor(1)]);
            idx = b.CreateSelect(br->getCondition(), idxt, idxf, "BrIdx");
        }
        else
        {
            idx = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
        }
        Value* agep = b.CreateGEP(arrtype, addrtable, {zero32, idx}, "BrAGep");
        Value* cgep = b.CreateGEP(arrtype, combinedtable, {zero32, idx}, "BrCGep");
        Value* loaded = b.CreateLoad(i64, agep, "BrLoad");
        Value* combined = b.CreateLoad(i64, cgep, "BrCombined");
        Value* effmask = b.CreateXor(combined, k, "BrEMask");
        Value* dec = b.CreateSub(loaded, effmask, "BrDec");
        Value* tgt = b.CreateIntToPtr(dec, ptrt, "BrP");

        SmallVector<BasicBlock*, 2> succs;
        for (BasicBlock* sc : br->successors()) succs.push_back(sc);
        auto* ibr = IndirectBrInst::Create(tgt, succs.size(), br);
        for (BasicBlock* sc : succs) ibr->addDestination(sc);
        ibr->copyMetadata(*br);
        br->eraseFromParent();
    }

    return !toindirect.empty();
}

static bool ShouldEncryptGVOperand(GlobalVariable* gv)
{
    if (!gv) return false;
    if (gv->getName().starts_with("llvm.")) return false;
    if (gv->getName().starts_with("__cond_stomp_")) return false;
    if (gv->isThreadLocal()) return false;
    // string literal GVs are handled by EncryptGatedStringsInRegion / the string pass; letting them through here would double encrypt 
    if (gv->isConstant() && gv->hasInitializer())
    {
        if (auto* arrt = dyn_cast<ArrayType>(gv->getValueType()))
        {
            Type* elemt = arrt->getElementType();
            if ((elemt->isIntegerTy(8) || elemt->isIntegerTy(16)) && isa<ConstantDataSequential>(gv->getInitializer()))
                return false;
        }
    }
    return true;
}

static bool EncryptGatedPointersInRegion(Function& f, const Site& s, ArrayRef<BasicBlock*> region, Value* k, uint64_t kct)
{
    if (!EncPointers) return false;
    if (!k || !s.TrueBB) return false;

    Module* m = f.getParent();
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* ptrt = PointerType::get(c, 0);
    MDNode* chainmark = MDNode::get(c, {MDString::get(c, "cs.gvp_chain")});

    DenseMap<GlobalVariable*, Value*> enccache;

    auto encgv = [&](GlobalVariable* gv) -> Value*
    {
        auto it = enccache.find(gv);
        if (it != enccache.end()) return it->second;

        uint64_t mask = NextCondStompMask();
        Constant* addr = ConstantExpr::getPtrToInt(gv, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        Constant* combined = ConstantInt::get(i64, mask ^ kct);

        auto* holder = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__cond_stomp_gv_ref");
        holder->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

        IRBuilder<> bs(s.TrueBB->getTerminator());
        Value* loaded = bs.CreateLoad(i64, holder, "GvpLoad");
        Value* effmask = bs.CreateXor(combined, k, "GvpEMask");
        Value* dec = bs.CreateSub(loaded, effmask, "GvpDec");
        Value* p = bs.CreateIntToPtr(dec, ptrt, "GvpP");
        if (auto* ii = dyn_cast<Instruction>(loaded))  ii->setMetadata("cs.gvp_chain", chainmark);
        if (auto* ii = dyn_cast<Instruction>(effmask)) ii->setMetadata("cs.gvp_chain", chainmark);
        if (auto* ii = dyn_cast<Instruction>(dec))     ii->setMetadata("cs.gvp_chain", chainmark);
        if (auto* ii = dyn_cast<Instruction>(p))       ii->setMetadata("cs.gvp_chain", chainmark);

        enccache[gv] = p;
        return p;
    };

    struct Task
    {
        Instruction* User;
        unsigned OpIdx;
        GlobalVariable* Gv;
        GEPOperator* GepCE;
    };
    std::vector<Task> tasks;

    for (BasicBlock* bb : region)
    {
        
        if (bb == s.TrueBB) continue;

        for (Instruction& i : *bb)
        {
            if (i.getMetadata("cs.gvp_chain")) continue;
            if (isa<IntrinsicInst>(&i)) continue;

            const unsigned nops = i.getNumOperands();
            for (unsigned oi = 0; oi != nops; ++oi)
            {
                if (auto* cb = dyn_cast<CallBase>(&i))
                    if (oi == cb->getCalledOperandUse().getOperandNo())
                        continue;

                Value* op = i.getOperand(oi);

                if (auto* gv = dyn_cast<GlobalVariable>(op))
                {
                    if (!ShouldEncryptGVOperand(gv)) continue;
                    tasks.push_back({&i, oi, gv, nullptr});
                    continue;
                }
                if (auto* ce = dyn_cast<GEPOperator>(op))
                {
                    if (isa<Instruction>(ce)) continue;
                    if (auto* gv = dyn_cast<GlobalVariable>(ce->getPointerOperand()))
                    {
                        if (!ShouldEncryptGVOperand(gv)) continue;
                        tasks.push_back({&i, oi, gv, ce});
                    }
                }
            }
        }
    }

    for (const Task& t : tasks)
    {
        Value* encbase = encgv(t.Gv);
        Value* newop;
        if (t.GepCE)
        {
            IRBuilder<> b(t.User);
            SmallVector<Value*, 4> indices;
            for (auto& idx : t.GepCE->indices()) indices.push_back(idx);
            Type* srct = t.GepCE->getSourceElementType();
            Value* gep = b.CreateGEP(srct, encbase, indices, "GvpGep");
            if (t.GepCE->isInBounds())
                if (auto* asgep = dyn_cast<GetElementPtrInst>(gep))
                    asgep->setIsInBounds(true);
            newop = gep;
        }
        else
        {
            newop = encbase;
        }
        t.User->setOperand(t.OpIdx, newop);
    }

    return !tasks.empty();
}

// InlineFunction bypasses AlwaysInline/NoInline/OptimizeNone
static bool ShouldInlineForStomp(CallInst* call)
{
    if (call->isMustTailCall()) return false;
    Function* callee = call->getCalledFunction();
    if (!callee) return false;
    if (callee->isDeclaration()) return false;
    if (callee->isIntrinsic()) return false;
    if (callee->isVarArg()) return false;
    if (callee->getName().starts_with("__cond_stomp_")) return false;
    if (callee == call->getFunction()) return false;
    if (HasAnnotation(*callee, "noobfus")) return false;
    if (CalleeBlockCount(callee) > MaxCalleeBlocks) return false;
    return true;
}

static uint64_t CompileStrHash(ArrayRef<uint64_t> chars)
{
    uint64_t h = 5381;
    for (uint64_t c : chars) h = h * 33 + c;
    return h;
}

static bool ExtractCString(Value* arg, unsigned charsize, std::vector<uint64_t>& outchars)
{
    // only accept all zero indices on the GEP wrapper
    while (auto* ce = dyn_cast<GEPOperator>(arg))
    {
        for (auto& idx : ce->indices())
        {
            auto* ci = dyn_cast<ConstantInt>(idx);
            if (!ci || !ci->isZero()) return false;
        }
        arg = ce->getPointerOperand();
    }

    auto* gv = dyn_cast<GlobalVariable>(arg);
    if (!gv || !gv->isConstant() || !gv->hasInitializer()) return false;

    auto* init = dyn_cast<ConstantDataSequential>(gv->getInitializer());
    if (!init) return false;

    Type* elemt = init->getElementType();
    if (!elemt->isIntegerTy()) return false;
    unsigned elembits = elemt->getIntegerBitWidth();
    if (elembits != charsize * 8) return false;

    outchars.clear();
    unsigned n = init->getNumElements();
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t c = init->getElementAsInteger(i);
        if (c == 0) break;
        outchars.push_back(c);
    }
    return true;
}

// AlwaysInline + InternalLinkage so a later AlwaysInlinerPass folds the loop into every string site rather than leaving a real function call
static Function* GetOrCreateStrHasher(Module& m, bool wide)
{
    const char* name = wide ? "__cond_stomp_hash_wstr" : "__cond_stomp_hash_str";
    if (Function* existing = m.getFunction(name)) return existing;

    LLVMContext& c = m.getContext();
    Type* i8 = Type::getInt8Ty(c);
    Type* i16 = Type::getInt16Ty(c);
    Type* i64 = Type::getInt64Ty(c);
    Type* chart = wide ? i16 : i8;
    PointerType* ptrt = PointerType::get(c, 0);

    FunctionType* ft = FunctionType::get(i64, {ptrt}, false);
    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, name, &m);
    f->addFnAttr(Attribute::AlwaysInline);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::WillReturn);
    f->getArg(0)->setName("S");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* loop = BasicBlock::Create(c, "Loop", f);
    BasicBlock* body = BasicBlock::Create(c, "Body", f);
    BasicBlock* exit = BasicBlock::Create(c, "Exit", f);

    IRBuilder<> b(entry);
    b.CreateBr(loop);

    b.SetInsertPoint(loop);
    PHINode* pphi = b.CreatePHI(ptrt, 2, "P");
    PHINode* hphi = b.CreatePHI(i64, 2, "H");
    Value* ch = b.CreateLoad(chart, pphi, "C");
    Value* isnul = b.CreateICmpEQ(ch, ConstantInt::get(chart, 0), "IsNul");
    b.CreateCondBr(isnul, exit, body);

    b.SetInsertPoint(body);
    Value* cz = b.CreateZExt(ch, i64, "Cz");
    Value* h33 = b.CreateMul(hphi, ConstantInt::get(i64, 33), "H33");
    Value* hnew = b.CreateAdd(h33, cz, "HNew");
    Value* pnext = b.CreateGEP(chart, pphi, ConstantInt::get(i64, 1), "PNext");
    b.CreateBr(loop);

    pphi->addIncoming(f->getArg(0), entry);
    pphi->addIncoming(pnext, body);
    hphi->addIncoming(ConstantInt::get(i64, 5381), entry);
    hphi->addIncoming(hnew, body);

    b.SetInsertPoint(exit);
    b.CreateRet(hphi);

    return f;
}

// strcmp/wcscmp only. null terminated fixed shape; strncmp/wcsncmp/memcmp with a constant N would need a length bounded hasher
static bool TryDetectStringSite(Module& m, BranchInst* br, std::vector<Site>& out)
{
    if (!br->isConditional()) return false;

    auto* cmp = dyn_cast<ICmpInst>(br->getCondition());
    if (!cmp || !cmp->hasOneUse()) return false;
    if (*cmp->user_begin() != br) return false;

    const CmpInst::Predicate p = cmp->getPredicate();
    if (p != CmpInst::ICMP_EQ && p != CmpInst::ICMP_NE) return false;

    Value* lhs = cmp->getOperand(0);
    Value* rhs = cmp->getOperand(1);
    auto* zeroci = dyn_cast<ConstantInt>(rhs);
    Value* callside = lhs;
    if (!zeroci || !zeroci->isZero())
    {
        zeroci = dyn_cast<ConstantInt>(lhs);
        callside = rhs;
        if (!zeroci || !zeroci->isZero()) return false;
    }

    auto* callinst = dyn_cast<CallInst>(callside);
    if (!callinst || !callinst->hasOneUse()) return false;
    if (*callinst->user_begin() != cmp) return false;

    Function* callee = callinst->getCalledFunction();
    if (!callee) return false;
    StringRef fname = callee->getName();
    bool wide;
    if      (fname == "strcmp"  || fname == "_strcmp")  wide = false;
    else if (fname == "wcscmp"  || fname == "_wcscmp")  wide = true;
    else return false;

    if (callinst->arg_size() != 2) return false;

    Value* a0 = callinst->getArgOperand(0);
    Value* a1 = callinst->getArgOperand(1);
    unsigned charsize = wide ? 2u : 1u;

    std::vector<uint64_t> chars;
    Value* runtimev = nullptr;
    if (ExtractCString(a1, charsize, chars))
    {
        runtimev = a0;
        std::vector<uint64_t> otherchars;
        
        if (ExtractCString(a0, charsize, otherchars)) return false;
    }
    else if (ExtractCString(a0, charsize, chars))
    {
        runtimev = a1;
    }
    else
    {
        return false;
    }

    const uint64_t precomp = CompileStrHash(chars);

    Function* hasher = GetOrCreateStrHasher(m, wide);

    IRBuilder<> b1(callinst);
    Value* hashresult = b1.CreateCall(hasher, {runtimev}, "SHash");

    IRBuilder<> b2(cmp);
    LLVMContext& c = cmp->getContext();
    Value* precompv = ConstantInt::get(Type::getInt64Ty(c), precomp);
    Value* newcmp = b2.CreateICmp(p, hashresult, precompv, "SCmp");

    cmp->replaceAllUsesWith(newcmp);
    cmp->eraseFromParent();
    callinst->eraseFromParent();

    const unsigned gateidx = (p == CmpInst::ICMP_EQ) ? 0u : 1u;

    Site s;
    s.Term = br;
    s.Cmp = cast<CmpInst>(newcmp);
    s.V = runtimev;
    s.CBits = precomp;
    s.BitWidth = 64;
    s.IsFP = false;
    s.IsString = true;
    s.StringHashK = hashresult;
    s.GateSuccIdx = gateidx;
    s.PreSplitTrueBB = br->getSuccessor(gateidx);
    s.TrueBB = nullptr;
    s.PreSplitPredCount = CountPreds(s.PreSplitTrueBB);
    out.push_back(s);
    return true;
}

static void CollectSites(Function& f, std::vector<Site>& out)
{
    for (BasicBlock& bb : f)
    {
        Instruction* term = bb.getTerminator();

        if (auto* br = dyn_cast<BranchInst>(term))
        {
            if (!br->isConditional()) continue;

            
            if (auto* condi = dyn_cast<Instruction>(br->getCondition()))
                if (IsStomped(condi)) continue;

            if (TryDetectStringSite(*f.getParent(), br, out)) continue;
            if (TryDetectCompoundSite(br, out)) continue;

            auto* cmp = dyn_cast<CmpInst>(br->getCondition());
            if (!cmp) continue;
            if (IsStomped(cmp)) continue;

            const CmpInst::Predicate p = cmp->getPredicate();

            
            const bool iseq = (p == CmpInst::ICMP_EQ);
            const bool isne = (p == CmpInst::ICMP_NE);
            const bool isfeq = (p == CmpInst::FCMP_OEQ);
            const bool isfne = (p == CmpInst::FCMP_UNE);
            if (!iseq && !isne && !isfeq && !isfne) continue;

            const bool isfp = (isfeq || isfne);
            const unsigned gateidx = (iseq || isfeq) ? 0u : 1u;

            Value* lhs = cmp->getOperand(0);
            Value* rhs = cmp->getOperand(1);

            Constant* cconst = dyn_cast<Constant>(rhs);
            Value* v = lhs;
            if (!cconst) { cconst = dyn_cast<Constant>(lhs); v = rhs; }
            if (!cconst || isa<Constant>(v)) continue;

            uint64_t cbits = 0;
            unsigned bw = 0;

            if (isfp)
            {
                if (!v->getType()->isFloatTy() && !v->getType()->isDoubleTy()) continue;

                auto* cfp = dyn_cast<ConstantFP>(cconst);
                if (!cfp) continue;

                const APFloat& apf = cfp->getValueAPF();
              
                if (apf.isNaN() || apf.isZero()) continue;

                const APInt bits = apf.bitcastToAPInt();
                bw = bits.getBitWidth();
                if (bw != 32 && bw != 64) continue;
                cbits = bits.getZExtValue();
            }
            else
            {
                auto* ci = dyn_cast<ConstantInt>(cconst);
                if (!ci) continue;
                if (!v->getType()->isIntegerTy()) continue;
                bw = ci->getBitWidth();
                if (bw < 8 || bw > 64) continue;
                cbits = ci->getZExtValue();
            }

            Site s;
            s.Term = br;
            s.Cmp = cmp;
            s.V = v;
            s.CBits = cbits;
            s.BitWidth = bw;
            s.IsFP = isfp;
            s.GateSuccIdx = gateidx;
            s.PreSplitTrueBB = br->getSuccessor(gateidx);
            s.TrueBB = nullptr;
            s.PreSplitPredCount = CountPreds(s.PreSplitTrueBB);
            out.push_back(s);
            continue;
        }

        if (auto* sw = dyn_cast<SwitchInst>(term))
        {
            Value* v = sw->getCondition();
            if (!v->getType()->isIntegerTy()) continue;
            const unsigned bw = v->getType()->getIntegerBitWidth();
            if (bw < 8 || bw > 64) continue;
            if (isa<Constant>(v)) continue;

            for (auto cs : sw->cases())
            {
                ConstantInt* ci = cs.getCaseValue();
                if (!ci) continue;

                const unsigned gateidx = cs.getSuccessorIndex();
                BasicBlock* succ = sw->getSuccessor(gateidx);

               
                if (succ && succ->getTerminator() && IsStomped(succ->getTerminator())) continue;

                Site s;
                s.Term = sw;
                s.Cmp = nullptr;
                s.V = v;
                s.CBits = ci->getZExtValue();
                s.BitWidth = bw;
                s.IsFP = false;
                s.GateSuccIdx = gateidx;
                s.PreSplitTrueBB = succ;
                s.TrueBB = nullptr;
                s.PreSplitPredCount = CountPreds(s.PreSplitTrueBB);
                out.push_back(s);
            }
        }
    }
}


static bool SplitAndCollectRegion(Site& s, DominatorTree& dt, LoopInfo& li, std::vector<BasicBlock*>& region)
{
    if (!s.Term || !s.Term->isTerminator()) return false;
    if (s.Term->getNumSuccessors() <= s.GateSuccIdx) return false;

    if (s.Cmp)
    {
        auto* br = dyn_cast<BranchInst>(s.Term);
        if (!br || !br->isConditional() || br->getCondition() != s.Cmp) return false;
    }

    s.PreSplitTrueBB = s.Term->getSuccessor(s.GateSuccIdx);
    if (!s.PreSplitTrueBB) return false;

    BasicBlock* pred = s.Term->getParent();
    if (!pred || pred->getTerminator() != s.Term) return false;

    const bool predisloopheader = li.getLoopFor(pred) && li.getLoopFor(pred)->getHeader() == pred;
    if (predisloopheader && SkipLoops) return false;

    CriticalEdgeSplittingOptions opts(&dt, &li);
    BasicBlock* newt = SplitCriticalEdge(s.Term, s.GateSuccIdx, opts);
    if (!newt)
    {
        if (s.PreSplitTrueBB->getUniquePredecessor() == pred)
            newt = s.PreSplitTrueBB;
        else
            return false;
    }
    s.TrueBB = newt;

    for (BasicBlock& bb : *pred->getParent())
        if (dt.dominates(newt, &bb))
            region.push_back(&bb);

    if (region.size() < MinRegion) return false;
    return true;
}

static Value* WidenToI64(Value* v, IRBuilder<>& b, const Twine& tag)
{
    LLVMContext& c = b.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* t = v->getType();

    if (t == i64) return v;
    if (t->isIntegerTy()) return b.CreateZExt(v, i64, tag + "Z64");
    if (t->isFloatTy())
    {
        Value* v32 = b.CreateBitCast(v, Type::getInt32Ty(c), tag + "Bc32");
        return b.CreateZExt(v32, i64, tag + "Z64");
    }
    if (t->isDoubleTy()) return b.CreateBitCast(v, i64, tag + "Bc64");
    return nullptr;
}

static Value* EmitARXEncryptRuntime(Value* vi64, uint64_t kconst, unsigned val1, unsigned val2, IRBuilder<>& b, const Twine& tag)
{
    Type* i64 = vi64->getType();
    Value* k = ConstantInt::get(i64, kconst);

    Value* x = b.CreateAdd(vi64, k, tag + "Add1");
    x = b.CreateOr(b.CreateShl(x, val1), b.CreateLShr(x, 64 - val1), tag + "Rol");
    x = b.CreateXor(x, k, tag + "Xor");
    x = b.CreateAdd(x, k, tag + "Add2");
    x = b.CreateOr(b.CreateShl(x, 64 - val2), b.CreateLShr(x, val2), tag + "Ror");
    return x;
}

static uint64_t CompileKDF(uint64_t v)
{
    return CompileARX(v, ARX.KDFSalt, ARX.KDFVal1, ARX.KDFVal2);
}

// the inline asm launder is the barrier that stops SCCP folding K back to CompileKDF(C) on the V==C edge; without it the whole encryption collapses to constants at compile time and the attacker sees plaintext
static Value* EmitRuntimeKDF(Value* v, IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    Type* i64 = Type::getInt64Ty(c);

    Value* v64 = WidenToI64(v, b, "KV");
    if (!v64) return nullptr;

    FunctionType* asmty = FunctionType::get(i64, {i64}, false);
    InlineAsm* launder = InlineAsm::get(asmty, "mov $0, $1", "=r,r,~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
    Value* vop = b.CreateCall(launder, {v64}, "KVOp");

    return EmitARXEncryptRuntime(vop, ARX.KDFSalt, ARX.KDFVal1, ARX.KDFVal2, b, "K");
}

static void ReplaceEqualityWithHash(Site& s)
{
    IRBuilder<> b(s.Cmp);
    LLVMContext& c = s.Cmp->getContext();
    Type* i64 = Type::getInt64Ty(c);

    Value* v64 = WidenToI64(s.V, b, "V");
    if (!v64) return;

    FunctionType* asmty = FunctionType::get(i64, {i64}, false);
    InlineAsm* launder = InlineAsm::get(asmty, "mov $0, $1", "=r,r,~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
    Value* vop = b.CreateCall(launder, {v64}, "HVOp");

    Value* hv = EmitARXEncryptRuntime(vop, ARX.HashSalt, ARX.HashVal1, ARX.HashVal2, b, "H");

   
    const uint64_t hc = CompileARX(s.CBits, ARX.HashSalt, ARX.HashVal1, ARX.HashVal2);
    Value* hcv = b.getInt64(hc);

    CmpInst::Predicate p = s.Cmp->getPredicate();
    if      (p == CmpInst::FCMP_OEQ) p = CmpInst::ICMP_EQ;
    else if (p == CmpInst::FCMP_UNE) p = CmpInst::ICMP_NE;

    Value* newcmp = b.CreateICmp(p, hv, hcv, "HashCmp");
    s.Cmp->replaceAllUsesWith(newcmp);
    s.Cmp->eraseFromParent();
}

struct Rewrite
{
    Instruction* User;
    unsigned OpIdx;
    uint64_t OrigBits;
    unsigned BitWidth;
};

struct PhiRewrite
{
    PHINode* Phi;
    unsigned IncomingIdx;
    BasicBlock* IncomingBB;
    uint64_t OrigBits;
    unsigned BitWidth;
};


static bool IsRewritableConstOp(Instruction& i, unsigned opidx)
{
    if (isa<PHINode>(i)) return false;
    if (isa<BranchInst>(i)) return false;
    if (isa<SwitchInst>(i)) return false;
    if (isa<IndirectBrInst>(i)) return false;
    if (isa<LandingPadInst>(i)) return false;
    if (isa<FuncletPadInst>(i)) return false;
    if (isa<DbgInfoIntrinsic>(i)) return false;

    if (auto* call = dyn_cast<CallBase>(&i))
    {
        if (opidx >= call->arg_size()) return false;
        if (call->paramHasAttr(opidx, Attribute::ImmArg)) return false;
        return true;
    }

    if (auto* gep = dyn_cast<GetElementPtrInst>(&i))
    {
        if (opidx == 0) return false;
        auto gti = gep_type_begin(gep);
        auto end = gep_type_end(gep);
        for (unsigned k = 1; k < opidx && gti != end; ++k, ++gti) {}
        if (gti == end) return false;
        return gti.getStructTypeOrNull() == nullptr;
    }

    return true;
}

static void HarvestConstants(ArrayRef<BasicBlock*> region, std::vector<Rewrite>& out, std::vector<PhiRewrite>& phiout)
{
    DenseSet<const BasicBlock*> inregion(region.begin(), region.end());

    for (BasicBlock* bb : region)
    {
        for (Instruction& i : *bb)
        {
            if (auto* phi = dyn_cast<PHINode>(&i))
            {
                for (unsigned k = 0, e = phi->getNumIncomingValues(); k < e; ++k)
                {
                    BasicBlock* incbb = phi->getIncomingBlock(k);
                    if (!inregion.count(incbb)) continue;

                    auto* ci = dyn_cast<ConstantInt>(phi->getIncomingValue(k));
                    if (!ci) continue;
                    unsigned bw = ci->getBitWidth();
                    if (bw < 8 || bw > 64) continue;

                    PhiRewrite pr;
                    pr.Phi = phi;
                    pr.IncomingIdx = k;
                    pr.IncomingBB = incbb;
                    pr.OrigBits = ci->getZExtValue();
                    pr.BitWidth = bw;
                    phiout.push_back(pr);
                }
                continue;
            }

            for (unsigned k = 0, e = i.getNumOperands(); k < e; ++k)
            {
                if (!IsRewritableConstOp(i, k)) continue;
                auto* ci = dyn_cast<ConstantInt>(i.getOperand(k));
                if (!ci) continue;
                unsigned bw = ci->getBitWidth();
                if (bw < 8 || bw > 64) continue;

                Rewrite r;
                r.User = &i;
                r.OpIdx = k;
                r.OrigBits = ci->getZExtValue();
                r.BitWidth = bw;
                out.push_back(r);
            }
        }
    }
}

// XOR against an opaque runtime K (K = ARX(V.op, KDF_SALT, ...) where V.op is laundered through inline asm) means a static lifter sees `xor(cipher, unknown)` and can't invert without executing the KDF with the actual runtime V; i64 XOR with trunc at use lets one K serve every operand width uniformly
static void RewriteConstants(ArrayRef<Rewrite> rws, Value* k, uint64_t kct)
{
    for (const Rewrite& r : rws)
    {
        IRBuilder<> b(r.User);
        Type* t = r.User->getOperand(r.OpIdx)->getType();

        const uint64_t cipher = r.OrigBits ^ kct;
        Value* cipherc = b.getInt64(cipher);
        Value* dec64 = b.CreateXor(cipherc, k, "CstDec64");

        Value* dec = (t->getPrimitiveSizeInBits() == 64) ? dec64 : b.CreateTrunc(dec64, t, "CstDec");
        r.User->setOperand(r.OpIdx, dec);
    }
}

// K is defined at the top of TrueBB which dominates every region block
static void RewritePhiConstants(ArrayRef<PhiRewrite> phis, Value* k, uint64_t kct)
{
    for (const PhiRewrite& p : phis)
    {
        IRBuilder<> b(p.IncomingBB->getTerminator());
        Type* t = p.Phi->getType();

        const uint64_t cipher = p.OrigBits ^ kct;
        Value* cipherc = b.getInt64(cipher);
        Value* dec64 = b.CreateXor(cipherc, k, "PhiDec64");

        Value* dec = (t->getPrimitiveSizeInBits() == 64) ? dec64 : b.CreateTrunc(dec64, t, "PhiDec");
        p.Phi->setIncomingValue(p.IncomingIdx, dec);
    }
}

struct DeferredIndirect
{
    Site S;
    std::vector<BasicBlock*> Region;
    Value* K;
    uint64_t KCt;
};

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (f.getName().starts_with("__cond_stomp_")) return false;
    if (HasAnnotation(f, "noobfus")) return false;

    bool mutated = false;
    unsigned round = 0;

    
    std::vector<DeferredIndirect> deferred;

    while (round++ < MaxFixpointRounds)
    {
        std::vector<Site> sites;
        CollectSites(f, sites);
        if (sites.empty()) break;

      
        DominatorTree dt;
        dt.recalculate(f);
        LoopInfo li;
        li.analyze(dt);

        for (Site& s : sites)
        {
            std::vector<BasicBlock*> region;
            if (!SplitAndCollectRegion(s, dt, li, region)) continue;

            mutated = true;

            if (ForceInline)
            {
                for (unsigned depth = 0; depth < MaxInlineDepth; ++depth)
                {
                    std::vector<CallInst*> toinline;
                    for (BasicBlock* bb : region)
                        for (Instruction& i : *bb)
                            if (auto* call = dyn_cast<CallInst>(&i))
                                if (ShouldInlineForStomp(call))
                                    toinline.push_back(call);

                    if (toinline.empty()) break;

                    bool inlinedany = false;
                    for (CallInst* call : toinline)
                    {
                        InlineFunctionInfo ifi;
                        InlineResult res = InlineFunction(*call, ifi);
                        if (res.isSuccess()) inlinedany = true;
                    }

                    if (!inlinedany) break;

                    // inlining spliced callee bodies into the caller, so dominance from s.TrueBB has shifted
                    dt.recalculate(f);
                    li = LoopInfo{};
                    li.analyze(dt);
                    region.clear();
                    for (BasicBlock& bb : f)
                        if (dt.dominates(s.TrueBB, &bb))
                            region.push_back(&bb);

                    if (region.size() > MaxRegionForInline) break;
                }
            }

           
            {
                if (s.Cmp && !s.IsString)
                {
                    Value* lhs = s.Cmp->getOperand(0);
                    Value* rhs = s.Cmp->getOperand(1);
                    if      (isa<Constant>(rhs)) s.V = lhs;
                    else if (isa<Constant>(lhs)) s.V = rhs;
                    else continue;
                }
                else if (s.IsString)
                {
                    if (auto* hashcall = dyn_cast<CallInst>(s.StringHashK))
                        s.V = hashcall->getArgOperand(0);
                }
                else if (auto* sw = dyn_cast<SwitchInst>(s.Term))
                {
                    s.V = sw->getCondition();
                }
            }

            // hash replace fires for int/FP branch sites only
            if (s.Cmp && !s.IsString && !s.IsCompound)
                ReplaceEqualityWithHash(s);

            std::vector<Rewrite> rws;
            std::vector<PhiRewrite> phirws;
            HarvestConstants(region, rws, phirws);

            const bool needk = !rws.empty() || !phirws.empty() || EncStringsInRegion;

            if (needk)
            {
                Value* k = nullptr;
                uint64_t kct = 0;
                if (s.IsString)
                {
                    // the string hash call dominates the entire region and already equals precomp on the V==literal edge, so it serves as K directly and Kct is just CBits
                    k = s.StringHashK;
                    kct = s.CBits;
                }
                else
                {
                    IRBuilder<> b(&*s.TrueBB->getFirstInsertionPt());
                    k = EmitRuntimeKDF(s.V, b);
                    kct = CompileKDF(s.CBits);
                }

                if (k && (!rws.empty() || !phirws.empty()))
                {
                    RewriteConstants(rws, k, kct);
                    RewritePhiConstants(phirws, k, kct);
                }

                EncryptGatedStringsInRegion(f, s, region, k, kct);
                EncryptGatedPointersInRegion(f, s, region, k, kct);

                if (k && (IndirectCalls || IndirectJumps))
                    deferred.push_back({s, region, k, kct});
            }

            MarkSiteProcessed(s);
        }
    }

    // regions may overlap
    for (DeferredIndirect& d : deferred)
    {
        if (IndirectCallsInRegion(f, d.Region, d.K, d.KCt)) mutated = true;
        if (IndirectBranchesInRegion(f, d.S, d.Region, d.K, d.KCt)) mutated = true;
    }

    return mutated;
}

bool RunConditionStomping(Module& m)
{
    if (!CondStompEnable) return false;

    CalleeBlockCache.clear();
    ARXInit();

    bool mutated = false;
    for (Function& f : m)
        mutated |= ProcessFunction(f);

    return mutated;
}

PreservedAnalyses ConditionStompingPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunConditionStomping(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
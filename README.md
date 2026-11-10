# Condition Stomping Obfuscation
Built for LLVM 19.1 - Windows x64 <br> <br>

Fully preventing Static AI, Lifters, Symbolic execution is quite a statement, right? Within modern obfuscation, the feared combo of hell; that is claimed to be unsurmountable, right? <br>
Its a cake walk in reality. Incompetent, and ill educated devs are to blame for the confusion. Despite code obfuscation being around for ages, not a single commercial obfuscation dev has come up with the simplest and easiest solution to static analysis. <br>
Just use the programs own nondeterministic paths against the reverse engineer.<br>

So we have a condition, it is:
```c
if(SomeVal == 0x1000)
```

*  Despite it being pretty obvious how we would protect this, we can simply hash it. As of right now only 1 commercial obfuscator ships condition hashing ;(

```c
if(H(SomeVal) == 0xdeadbeef)
```

* Now we have obscured the value. This is the furthest people have realistically gotten with condition obfuscating. Lets take it a step further. <br>
* So you have no idea what 0xdeadbeef is in there, we know its 0x1000 from the unobfuscated comparison, but your attacker doesn't know that, because SomeVal is input dependent on your server code or user input. It is Nondeterministic! <br>
* We have a value only knowable by correct input values that could only be done if the runtime executed PERFECTLY to this point, everything executed to perfection, user input was collided with, EVERYTHING. <br>
* We know that inside that condition SomeVal is ALWAYS going to be 0x1000! <br>

```c
if(H(SomeVal) == 0xdeadbeef)
{
EncryptedInt xor SomeVal
EncryptedFloat xor SomeVal
SomeFunc();
SomeFunc1();
SomeFunc2();
}
```

* So now you have the function impossible to navigate as its contents are all encrypted at compile time to 0x1000, we decrypt it with SomeVal. <br>
* Why stop There? This is where it turns into STOMPING. <br>
* We inline EVERYTHING into that condition. That is exactly what we do here. We take every single condition gated path that has actual usage, and we force inline the living hell out of everything recursively, therefore making massive condition blocks. <br>

```c
if(H(SomeVal) == 0xdeadbeef)
{
EncryptedInt xor SomeVal
EncryptedFloat xor SomeVal
  SomeFunc()
  {
  SomeFunc body contents encrypted xor SomeVal
      SomeFunc4()
      {
       SomeFunc4 body contents encrypted xor SomeVal
      
      }
  }
  SomeFunc1()
  {
  SomeFunc1 body contents encrypted xor SomeVal
      SomeFunc5()
      {
       SomeFunc5 body contents encrypted xor SomeVal
      
      }
  }
  SomeFunc2()
  {
  SomeFunc2 body contents encrypted xor SomeVal
      SomeFunc6()
      {
       SomeFunc6 body contents encrypted xor SomeVal
      
      }
  }
}
```

## The drawbacks
*  There is only 1 single drawback, once the condition has been found at runtime, it is known, if you have a build server though, anything network based such as packetIDs and information can be changed per build. <br>
*  The performance overhead? Nonexistent, its basic xors, caching performance degrades to a tiny degree. File size will explode 200%. Reversing engineering will NEED to be dynamic on a lot of your code base. <br>
*  You can realistically deploy this on games if you just do constant encryption and keep it moderate enough.  Encrypt a few constants here and there, or mainly target things like strings that get sigscanned. There is no need for indirect jumping/calling, but GV, constants, strings are recommended.
*  We can't inline polymorphic functions (Classes, Callbacks). So C code is preferred! <br><br>
Yes, This is how poor the commercial binary obfuscation market is, its been decades, and not a single person running a binary obfuscation company came up with the idea of inlining conditions, and encrypting the contents with the unknown condition value. <br>
All it takes is 1 good server side check at the start of your program that is per build unique, and your attacker now has to attach a debugger or spam hooks, you can ban them and they can spend all day fighting your runtime protections.<br>


## Before
<img width="291" height="759" alt="image" src="https://github.com/user-attachments/assets/8e72bc12-87db-4c8a-be51-95928381e750" />
<img width="316" height="916" alt="image" src="https://github.com/user-attachments/assets/2bb8b0c7-463f-4a20-ac90-f7ec0ae561e6" />
<img width="294" height="663" alt="image" src="https://github.com/user-attachments/assets/caffc1b1-22cb-4afc-94b4-4d4a65a685dd" />

## After 
<img width="962" height="831" alt="image" src="https://github.com/user-attachments/assets/5e5de463-f767-4e09-a6a5-0b9b4061b91f" />
<img width="2057" height="815" alt="image" src="https://github.com/user-attachments/assets/a9b3223f-0015-4c89-b381-1d00e20dafe4" />
<img width="2045" height="592" alt="image" src="https://github.com/user-attachments/assets/a8357ca7-82ae-4cb2-a859-ca5f2b3dd333" />
<img width="1515" height="977" alt="image" src="https://github.com/user-attachments/assets/128f5c1b-5df3-4fe2-ae81-dd17962927a6" />
<img width="928" height="594" alt="image" src="https://github.com/user-attachments/assets/e0bf7088-788d-4d68-b798-99ddcd8eaa92" />


## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll

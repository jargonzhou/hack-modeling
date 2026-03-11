# WebAssembly
* https://webassembly.org/
* https://webassembly.org/specs/


> WebAssembly (abbreviated Wasm) is a binary instruction format for a stack-based virtual machine.
>
> Wasm is designed as a portable compilation target for programming languages, enabling deployment on the web for client and server applications.

actions
* https://github.com/jargonzhou/learning-frontend-stack/tree/main/language/WebAssembly


# Emscripten
* https://emscripten.org/
* [Emscripten SDK](https://github.com/emscripten-core/emsdk): The Emscripten toolchain is distributed as a standalone Emscripten SDK. The SDK provides all the required tools, such as Clang, Python and Node.js along with an update mechanism that enables migrating to newer Emscripten versions as they are released.
* [Emscripten Compiler Frontend (emcc)](https://emscripten.org/docs/tools_reference/emcc.html): Most clang options will work, as will gcc options.

Emscripten is **a complete compiler toolchain to WebAssembly**, using **LLVM**, with a special focus on speed, size, and the Web platform.

* **Porting**
Compile your existing projects written in C or C++ — or any language that uses [LLVM](http://llvm.org/) — to browsers, [Node.js](https://nodejs.org/), or [wasm runtimes](https://v8.dev/blog/emscripten-standalone-wasm#running-in-wasm-runtimes).
* **APIs**
Emscripten **converts OpenGL into WebGL**, and has support for familiar APIs like **SDL**, **pthreads**, and **POSIX**, as well as **Web APIs** and **JavaScript**.
* **Fast**
Thanks to the combination of LLVM, Emscripten, [Binaryen](https://github.com/WebAssembly/binaryen), and [WebAssembly](http://webassembly.org/), the output is compact and runs at near-native speed.

# Call Python code in JavaScript

* [pyodide](https://pyodide.org/)
    * [Loading packages](https://pyodide.org/en/stable/usage/loading-packages.html)
    * [matplotlib Examples > Lines, bars and markers > Filled polygon](https://matplotlib.org/stable/gallery/lines_bars_and_markers/fill.html#sphx-glr-gallery-lines-bars-and-markers-fill-py)

# Extism
* https://extism.org/
* https://github.com/extism/extism

The framework for building with WebAssembly (wasm). Easily load wasm modules, move data, call functions, and build extensible apps.

# See Also
* [WebAssembly * MDN](https://developer.mozilla.org/en-US/docs/WebAssembly)
* Gallant, Gerard. **WebAssembly in Action**. 2019. Manning.
* Sletten, Brian. **WebAssembly: The Definitive Guide**. 2021. O'Reilly Media.
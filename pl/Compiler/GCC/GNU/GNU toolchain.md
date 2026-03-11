# GNU toolchain
* https://en.wikipedia.org/wiki/GNU_toolchain


# glibc: core C library including headers, libraries, and dynamic loader
* https://gcc.gnu.org/
* Sandra Loosemore, Richard M. Stallman, Roland McGrath, Andrew Oram, and Ulrich Drepper. **The GNU C Library Reference Manual**'. version 2.34.

core C library including headers, libraries, and dynamic loader

* GNU Fortran
* CPP: The C Preprocessor
* GNAT: The GNU Ada Development Environment
* Standard C++ Library
* GCCGO
* GNU Offloading and Multi Processing Runtime Library
* Quad-Precision Math Library
* JIT Library: libgccjit, for embedding GCC inside programs and libraries

# GNU Autotools: Autoconf, Automake and Libtool
* https://en.wikipedia.org/wiki/GNU_Autotools
* Calcote, John. Autotools: A Practioner's Guide to GNU Autoconf, Automake, and Libtool. 2020, 2. edition. No Starch Press.

> The GNU Autotools, also known as **the GNU Build System**, is a suite of build automation tools designed to support building source code and packaging the resulting binaries. It supports building a codebase for multiple target systems without customizing or modifying the code. It is available on many Linux distributions and Unix-like environments.
>
> Autotools is part of the GNU toolchain and is widely used in many free software and open source packages. Its component tools are free software, licensed under the GNU General Public License with special license exceptions permitting its use with proprietary software.

Autotools consists of the GNU utilities **Autoconf**, **Automake**, and **Libtool**.

Other related tools include **GNU Make**, **GNU gettext**, **pkg-config**, and **GCC**.

# GNU Binutils: a suite of tools including linker, assembler and other tools
* https://www.gnu.org/software/binutils/

The GNU Binutils are a collection of binary tools. The main ones are:
- **ld** - the GNU linker.
- **as** - the GNU assembler.
- **gold** - a new, faster, ELF only linker.

But they also include:
- **addr2line** - Converts addresses into filenames and line numbers.
- **ar** - A utility for creating, modifying and extracting from archives.
- **c++filt** - Filter to demangle encoded C++ symbols.
- **dlltool** - Creates files for building and using DLLs.
- **elfedit** - Allows alteration of ELF format files.
- **gprof** - Displays profiling information.
- **[gprofng](https://sourceware.org/binutils/wiki/gprofng)** - Collects and displays application performance data.
- **nlmconv** - Converts object code into an NLM.
- **nm** - Lists symbols from object files.
- **objcopy** - Copies and translates object files.
- **objdump** - Displays information from object files.
- **ranlib** - Generates an index to the contents of an archive.
- **readelf** - Displays information from any ELF format object file.
- **size** - Lists the section sizes of an object or archive file.
- **strings** - Lists printable strings from files.
- **strip** - Discards symbols.
- **windmc** - A Windows compatible message compiler.
- **windres** - A compiler for Windows resource files.

As well as some libraries:
- **libbfd** - A library for manipulating binary files in a variety of different formats.
- **libctf** - A library for manipulating the CTF debug format.
- **libopcodes** - A library for assembling and disassembling a variety of different assembler languages.
- **libsframe** - A library for manipulating the SFRAME debug format.

Most of these programs use **BFD**, the Binary File Descriptor library, to do low-level manipulation. Many of them also use the **opcodes** library to assemble and disassemble machine instructions.

# GNU Bison: a parser generator, often used with the Flex lexical analyser

# GNU m4: an m4 macro processor

# GNU Make: an automation tool for compilation and build
* https://www.gnu.org/software/make/
* Robert Mecklenburg. **Managing Projects with GNU Make, Third Edition**'. O’Reilly Media, 2005.


# GDB: The GNU Project Debugger
* https://www.sourceware.org/gdb/

> What is GDB?
>
> GDB, the GNU Project debugger, allows you to see what is going on `inside' another program while it executes -- or what another program was doing at the moment it crashed.
>
> GDB can do four main kinds of things (plus other things in support of these) to help you catch bugs in the act:
> 
> - Start your program, specifying anything that might affect its behavior.
> - Make your program stop on specified conditions.
> - Examine what has happened, when your program has stopped.
> - Change things in your program, so you can experiment with correcting the effects of one bug and go on to learn about another.
> 
> Those programs might be executing on the same machine as GDB (native), on another machine (remote), or on a simulator. GDB can run on most popular > UNIX and Microsoft Windows variants, as well as on macOS.

> What Languages does GDB Support?
> 
> GDB supports the following languages (in alphabetical order):
> 
> - Ada
> - Assembly
> - C
> - C++
> - D
> - Fortran
> - Go
> - Objective-C
> - OpenCL
> - Modula-2
> - Pascal
> - Rust


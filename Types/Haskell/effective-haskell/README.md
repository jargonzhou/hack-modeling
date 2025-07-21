# Examples in 'Effective Haskell'

- 1 Getting Started with Haskell
- 2 Working with Lists
- 3 Getting Started with Types
- 4 Creating New Types
- 5 Creating And Structuring Haskell Projects
- 6 Type Classes
- 7 Understanding IO
- 8 Working with the Local System
- 9 Introducing Monads
- 10 Mutable Data in the Real World
- 11 Serializing Heterogenous Data
- 12 Deserializing Heterogenous Data
- 13 Building Applications with Many Effects
- 14 Building Efficient Programs
- 15 Programming with Types


## cabal

Create project:

```shell
# see ch05-projects
$ cabal init --interactive                                                      in cmd at 12:56:00
What does the package build:
   1) Library
 * 2) Executable
   3) Library and Executable
   4) Test suite
Your choice? [default: Executable] 3
Do you wish to overwrite existing files (backups will be created) (y/n)? [default: n]
Please choose version of the Cabal specification to use:
   1) 1.24  (legacy)
   2) 2.0   (+ support for Backpack, internal sub-libs, '^>=' operator)
   3) 2.2   (+ support for 'common', 'elif', redundant commas, SPDX)
   4) 2.4   (+ support for '**' globbing)
 * 5) 3.0   (+ set notation for ==, common stanzas in ifs, more redundant commas, better pkgconfig-depends)
   6) 3.4   (+ sublibraries in 'mixins', optional 'default-language')
Your choice? [default: 3.0] 4
Package name? [default: ch05-projects]
Package version? [default: 0.1.0.0]
Please choose a license:
   1) BSD-2-Clause
   2) BSD-3-Clause
   3) Apache-2.0
   4) MIT
   5) MPL-2.0
   6) ISC
   7) GPL-2.0-only
   8) GPL-3.0-only
   9) LGPL-2.1-only
  10) LGPL-3.0-only
  11) AGPL-3.0-only
  12) GPL-2.0-or-later
  13) GPL-3.0-or-later
  14) LGPL-2.1-or-later
  15) LGPL-3.0-or-later
  16) AGPL-3.0-or-later
  17) Other (specify)
Your choice? 4
Author name? [default: zhoujiagen]
Maintainer email? [default: zhoujiagen@gmail.com]
Project homepage URL? [optional]
Project synopsis? [optional] A sample project to learn cabal.
Project category:
   1) Codec
   2) Concurrency
   3) Control
   4) Data
   5) Database
   6) Development
   7) Distribution
   8) Game
   9) Graphics
  10) Language
  11) Math
  12) Network
  13) Sound
  14) System
  15) Testing
  16) Text
  17) Web
  18) Other (specify)
Your choice? [default: (none)]
Library source directory:
 * 1) src
   2) lib
   3) src-lib
   4) Other (specify)
Your choice? [default: src]
Choose a language for your library:
 * 1) Haskell2010
   2) Haskell98
   3) GHC2021 (requires at least GHC 9.2)
   4) Other (specify)
Your choice? [default: Haskell2010]
What is the main module of the executable:
 * 1) Main.hs
   2) Main.lhs
   3) Other (specify)
Your choice? [default: Main.hs]
Application directory:
 * 1) app
   2) exe
   3) src-exe
   4) Other (specify)
Your choice? [default: app]
Choose a language for your executable:
 * 1) Haskell2010
   2) Haskell98
   3) GHC2021 (requires at least GHC 9.2)
   4) Other (specify)
Your choice? [default: Haskell2010]
Should I generate a test suite for the library? [default: y]
What is the main module of the test suite?:
 * 1) Main.hs
   2) Main.lhs
   3) Other (specify)
Your choice? [default: Main.hs]
Test directory? [default: test]
Choose a language for your test suite:
 * 1) Haskell2010
   2) Haskell98
   3) GHC2021 (requires at least GHC 9.2)
   4) Other (specify)
Your choice? [default: Haskell2010]
Add informative comments to each field in the cabal file. (y/n)? [default: y]
[Log] Using cabal specification: 2.4
[Log] Creating fresh file LICENSE...
[Log] Creating fresh file CHANGELOG.md...
[Log] Creating fresh directory ./src...
[Log] Creating fresh file src\MyLib.hs...
[Log] Creating fresh directory ./app...
[Log] Creating fresh file app\Main.hs...
[Log] Creating fresh directory ./test...
[Log] Creating fresh file test\Main.hs...
[Log] Creating fresh file ch05-projects.cabal...
[Info] You may want to edit the .cabal file and add a Description field.
```

build, run, repl:

```shell
$ cabal clean
$ cabal build
Resolving dependencies...
Build profile: -w ghc-9.4.8 -O1
In order, the following will be built (use -v for more details):
 - ch05-projects-0.1.0.0 (lib) (first run)
 - ch05-projects-0.1.0.0 (exe:ch05-projects) (first run)
Configuring library for ch05-projects-0.1.0.0..
Preprocessing library for ch05-projects-0.1.0.0..
Building library for ch05-projects-0.1.0.0..
[1 of 1] Compiling MyLib            ( src\MyLib.hs, D:\\workspace\learning-haskell\effective-haskell\ch05-projects\dist-newstyle\build\x86_64-windows\ghc-9.4.8\ch05-projects-0.1.0.0\build\MyLib.o )
Configuring executable 'ch05-projects' for ch05-projects-0.1.0.0..
Preprocessing executable 'ch05-projects' for ch05-projects-0.1.0.0..
Building executable 'ch05-projects' for ch05-projects-0.1.0.0..
[1 of 1] Compiling Main             ( app\Main.hs, D:\\workspace\learning-haskell\effective-haskell\ch05-projects\dist-newstyle\build\x86_64-windows\ghc-9.4.8\ch05-projects-0.1.0.0\x\ch05-projects\build\ch05-projects\ch05-projects-tmp\Main.o )
[2 of 2] Linking D:\\workspace\\learning-haskell\\effective-haskell\\ch05-projects\\dist-newstyle\\build\\x86_64-windows\\ghc-9.4.8\\ch05-projects-0.1.0.0\\x\\ch05-projects\\build\\ch05-projects\\ch05-projects.exe  

$ cabal build lib:ch05-projects
$ cabal build exe:ch05-projects

$ cabal repl
Build profile: -w ghc-9.4.8 -O1
In order, the following will be built (use -v for more details):
 - ch05-projects-0.1.0.0 (lib) (ephemeral targets)
Preprocessing library for ch05-projects-0.1.0.0..
GHCi, version 9.4.8: https://www.haskell.org/ghc/  :? for help
Ok, one module loaded.
ghci> someFunc
someFunc

$ cabal exec ch05-projects
Hello, Haskell!
someFunc

$ cabal run ch05-projects
Hello, Haskell!
someFunc
```

doc:

```shell
$ cabal haddock
Resolving dependencies...
Build profile: -w ghc-9.4.8 -O1
In order, the following will be built (use -v for more details):
 - ch05-projects-0.1.0.0 (lib) (ephemeral targets)
Preprocessing library for ch05-projects-0.1.0.0..
Running Haddock on library for ch05-projects-0.1.0.0..
Warning: The documentation for the following packages are not installed. No
links will be generated to these packages: base-4.17.2.1, ghc-bignum-1.3,
ghc-prim-0.9.1
   0% (  0 /  2) in 'MyLib'
  Missing documentation for:
    Module header
    someFunc (src\MyLib.hs:3)
Warning: MyLib: could not find link destinations for:

        - GHC.Types.IO
Documentation created:
D:\workspace\learning-haskell\effective-haskell\ch05-projects\dist-newstyle\build\x86_64-windows\ghc-9.4.8\ch05-projects-0.1.0.0\doc\html\ch05-projects\
```
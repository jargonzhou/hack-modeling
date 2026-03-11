# Haskell Tools

# Core

* [ghcup](./GHCUP.md): The Haskell toolchain installer
* [ghc](./GHC.md): The Glasgow Haskell Compiler
* [cabal](./Cabal.md): The Cabal build tool for managing Haskell software
* [stack](./Stack.md): A cross-platform program for developing Haskell projects (similar to cabal)
* [hls](https://github.com/haskell/haskell-language-server): A language server for developers to integrate with their editor/IDE

# VSCode

* [Haskell for Visual Studio Code](https://marketplace.visualstudio.com/items?itemName=haskell.haskell)
    - [ghci-dap](https://github.com/phoityne/ghci-dap)
    - [haskell-debug-adapter](https://github.com/phoityne/haskell-debug-adapter)

```shell
cabal install ghci-dap haskell-debug-adapter
haskell-debug-adapter --version
```

* [Ormolu](https://hackage.haskell.org/package/ormolu): Ormolu is a formatter for Haskell source code.

```shell
cabal install ormolu
```

* [stylish-haskell](https://github.com/haskell/stylish-haskell): Haskell code prettifier.

```shell
cabal install stylish-haskell
stylish-haskell --version
```

* [IHaskell](https://github.com/IHaskell/IHaskell): A Haskell kernel for the Jupyter project.

# Others

* [commercialhaskell/stackage-snapshots](https://github.com/commercialhaskell/stackage-snapshots): LTS Haskell and Stackage Nightly snapshot configurations (experimental, for pantry). `ghc-xxx`, `lts-xxx`
    - [Stackage](https://www.stackage.org/): Stable Haskell package sets
* [Hackage](https://hackage.haskell.org/): The Haskell Package Repository
    - [base](https://hackage.haskell.org/package/base): Core data structures and operations
* [Haddock](https://gitlab.haskell.org/ghc/ghc/-/tree/master/utils/haddock): the standard tool for generating documentation from Haskell code.
    - [Haddocks for Libraries included with GHC](https://downloads.haskell.org/~ghc/latest/docs/html/libraries/index.html)
* [haskell/process](https://github.com/haskell/process): Library for dealing with system processes.
* [Haskell Playground](https://play.haskell.org/)
* [Hoogle API Search](http://www.haskell.org/hoogle/): Hoogle is a Haskell API search engine, which allows you to search the Haskell libraries on Stackage by either function name, or by approximate type signature.
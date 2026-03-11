# GHCUP
https://www.haskell.org/ghcup/

> The Haskell toolchain installer

tui:
```shell
# text-based user interface
ghcup tui
# Windows: ghcup: thread blocked indefinitely in an STM transaction
# Use Git Bash instead
```

```shell
# list available ghc/cabal versions
ghcup list

# install the recommended GHC version
ghcup install ghc

# install a specific GHC version
ghcup install ghc 8.2.2
# with cache
ghcup install hls 2.6.0.0 -c

# set the currently "active" GHC version
ghcup set ghc 8.4.4

# install cabal-install
ghcup install cabal

# update ghcup itself
ghcup upgrade
```

uninstall:
```shell
ghcup nuke
```
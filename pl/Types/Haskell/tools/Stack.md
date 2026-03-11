# Stack
* https://docs.haskellstack.org/en/stable/

> A cross-platform program for developing Haskell projects (similar to cabal)

* [Configuration files](https://docs.haskellstack.org/en/stable/configure/yaml/)
* [hpack](https://github.com/sol/hpack): Hpack is a format for Haskell packages. It is a modern alternative to the Cabal package format and follows different design principles.

`ERROR` stack commitAndReleaseBuffer: invalid argument (cannot encode character '\8226')

`SOLUTION` Windows: 时间和语言 > 语言和区域 > 相关设置 管理语言设置 > 更改系统区域设置 > 勾选 Beta版 使用UTF-8 (需要重启电脑)

```shell
$ stack update # Update the package index.

$ stack new <project-name> # Create a new project from a template.
$ cd <project-name>
$ stack setup # Get the appropriate GHC for your project.
$ stack build # Build the package(s) in this directory/configuration

$ stack repl # Run ghci in the context of package(s) (alias for 'ghci').
$ stack exec # Execute a command. If the command is absent, the first of any arguments is taken as the command.
$ stack test # Shortcut for 'build --test'

# path
$ stack path

$ dependencies
stack ls dependencies --help
```

# See Also
* [haskeleton](https://github.com/tfausak/haskeleton): This project is unmaintained! Haskeleton is now available as a Stack template.
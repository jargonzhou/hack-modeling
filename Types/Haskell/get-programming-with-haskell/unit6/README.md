# Unit 6 Organizing code and building projects

## Lesson 35 Building projects with stack

- palindrome-checker

> MacOS.

1. Update stack indexes

```shell
➜  lesson35 git:(main) stack --version
Version 2.13.1, Git revision 8102bb8afce90fc954f48efae38b87f37cabc988 x86_64 hpack-0.36.0
➜  lesson35 git:(main) stack update

Warning: You are currently using Stack version 2.13.1 but version 2.15.1 is available.
         
         You can try to upgrade by running stack upgrade
         
         Tired of seeing this? Add recommend-stack-upgrade: false to /Users/zhang/.stack/config.yaml.
         
         
Selected mirror https://hackage.haskell.org/
Downloading timestamp
Downloading snapshot
Updating index
Waiting to acquire cache lock on /Users/zhang/.stack/pantry/hackage/hackage-security-lock
Acquired cache lock on /Users/zhang/.stack/pantry/hackage/hackage-security-lock
Released cache lock on /Users/zhang/.stack/pantry/hackage/hackage-security-lock
Updated package index downloaded
Calculating hashes to check for hackage-security rebases or filesystem changes
Updating preexisting cache, should be quick
Populating cache from file size 897692160, hash 1f2a9c9dc99353fd7e360c7ea1687f5180f14a56ca35d1e584a68aa21adbb58b
Populating package index cache ...
Package index cache populated
```

2. Create new project

```shell
➜  lesson35 git:(main) stack new palindrome-checker
Downloading template new-template to create project palindrome-checker in directory palindrome-checker/...
Downloaded /Users/zhang/.stack/templates/new-template.hsfiles.               

Note: The following parameters were needed by the template but not provided: author-email, author-name, category, copyright and github-username.
      
      You can provide them in Stack's global YAML configuration file (/Users/zhang/.stack/config.yaml) like this:
      
      templates:
        params:
          author-email: value
          author-name: value
          category: value
          copyright: value
          github-username: value
      
      Or you can pass each one on the command line as parameters like this:
      
      stack new palindrome-checker new-template -p "author-email:value" -p "author-name:value" -p "category:value" -p "copyright:value" -p
      "github-username:value"
      
Looking for Cabal or package.yaml files to use to initialise Stack's project-level YAML configuration file.

Using the Cabal packages:
* palindrome-checker/

Selecting the best among 21 snapshots...


Note: Matches https://raw.githubusercontent.com/commercialhaskell/stackage-snapshots/master/lts/22/11.yaml
      
Selected the snapshot https://raw.githubusercontent.com/commercialhaskell/stackage-snapshots/master/lts/22/11.yaml.
Initialising Stack's project-level YAML configuration file using snapshot
https://raw.githubusercontent.com/commercialhaskell/stackage-snapshots/master/lts/22/11.yaml.
Considered 1 user package.
Writing configuration to palindrome-checker/stack.yaml.
Stack's project-level YAML configuration file has been initialised.

➜  lesson35 git:(main) ✗ tree
.
├── README.md
└── palindrome-checker
    ├── CHANGELOG.md
    ├── LICENSE
    ├── README.md
    ├── Setup.hs
    ├── app
    │   └── Main.hs
    ├── package.yaml
    ├── palindrome-checker.cabal
    ├── src
    │   └── Lib.hs
    ├── stack.yaml
    └── test
        └── Spec.hs

4 directories, 11 files
```

3. Setup stack

```shell
➜  palindrome-checker git:(main) ✗ stack setup
Stack will use the GHC on your PATH. For more information on paths, see stack path and stack exec env. To use this GHC and packages outside of a project,
consider using: stack ghc, stack ghci, stack runghc, or stack exec.
```

4. Build and execute

```shell
➜  palindrome-checker git:(main) ✗ stack build
palindrome-checker-0.1.0.0: unregistering (local file changes: app/Main.hs src/Lib.hs)
palindrome-checker> build (lib + exe)
Preprocessing library for palindrome-checker-0.1.0.0..
Building library for palindrome-checker-0.1.0.0..
[1 of 2] Compiling Lib [Source file changed]
Preprocessing executable 'palindrome-checker-exe' for palindrome-checker-0.1.0.0..
Building executable 'palindrome-checker-exe' for palindrome-checker-0.1.0.0..
[1 of 2] Compiling Main [Source file changed]
[3 of 3] Linking .stack-work/dist/x86_64-osx/ghc-9.6.4/build/palindrome-checker-exe/palindrome-checker-exe [Objects changed]
palindrome-checker> copy/register
Installing library in /Users/zhang/workspace/github/learning-haskell/get-programming-with-haskell/unit7/lesson35/palindrome-checker/.stack-work/install/x86_64-osx/46273dff38774613909873b7a6e346737b12f1448d0e1cc0e8f44cae8fca2d50/9.6.4/lib/x86_64-osx-ghc-9.6.4/palindrome-checker-0.1.0.0-2w9iSycfp3T4OttWe8NbRL
Installing executable palindrome-checker-exe in /Users/zhang/workspace/github/learning-haskell/get-programming-with-haskell/unit7/lesson35/palindrome-checker/.stack-work/install/x86_64-osx/46273dff38774613909873b7a6e346737b12f1448d0e1cc0e8f44cae8fca2d50/9.6.4/bin
Registering library for palindrome-checker-0.1.0.0..

➜  palindrome-checker git:(main) ✗ stack exec palindrome-checker-exe
Enter a word and I'll let you know if it's a palindrome!
A man, a plan, a canal: Panama!
it is!
```

## Lesson 36 Property testing with QuickCheck

- palindrome-testing

```shell
$ stack test
palindrome-testing> test (suite: palindrome-testing-test)

Running tests...
passed 'racecar'
passed 'racecar!'
passed 'cat'
tests done!
Running QuickCheck...
+++ OK, passed 100 tests.
+++ OK, passed 3 tests.
Passed:
""

Passed:
"\151925\EOTz>\1101694"

Passed:
"M\163755zh~\30874G\DC3\185495\&3D\CAN\1102876Vq\DELm\1098578\993464<\160452&#,\a$\1053778\171116\f\ETX@PI\100162!RI\1066939\\zajCO l\NAKT\NAK"

+++ OK, passed 3 tests.
Passed:
""

Passed:
"\151925\EOTz>\1101694"

Passed:
"M\163755zh~\30874G\DC3\185495\&3D\CAN\1102876Vq\DELm\1098578\993464<\160452&#,\a$\1053778\171116\f\ETX@PI\100162!RI\1066939\\zajCO l\NAKT\NAK"

+++ OK, passed 3 tests.

QuickCheck done!

palindrome-testing> Test suite palindrome-testing-test passed
```
# Runs

## `Hello.idr`

- Idris 1
```shell
Idris> :cd ch01
Idris> :l Hello
*Hello> :exec
Hello, Idris World!
*Hello>
```

- Idris 2
```shell

Main> -- the interactive environment
Main> the Double 2.1 * 20
42.0
Main> 
Main> 6 + 8 * 11
94
Main> 2.1 * 20
Error: Can't find an implementation for FromDouble Integer.

(Interactive):1:1--1:4
 1 | 2.1 * 20
     ^^^

Main> "Hello" ++ " " ++ "World!"
"Hello World!"
Main> reverse "abcdefg"
"gfedcba"

Main> -- checking types
Main> :t 2 + 2
2 + 2 : Integer
Main> :t "Hello!"    
fromString "Hello!" : String
Main> :t Integer
Integer : Type
Main> :t String
String : Type
Main> :t Type
Type : Type

Main> -- compile and run programs
Main> :cd "ch01"
Current working directory is ".../type-driven-dev-idris/ch01"
Main> :l "Hello.idr"
1/1: Building Hello (Hello.idr)
Loaded file Hello.idr
Main> :exec main
Hello, Idris World!

$ idris2 Hello.idr --exec m
ain
Hello, Idris World!

$ idris2 Hello.idr -o Hello
$ ./build/exec/Hello
Hello, Idris World!
```

## FCTypes.idr

```shell
$ rlwrap idris2
Main> :l "FCTypes.idr"
Loaded file FCTypes.idr
Main> valToString False $ getStringOrInt False
"Ninety four"
Main> valToString True $ getStringOrInt True
"94"
```
# Code of 'Type-Driven Development with Idris'

- Idris 1
```shell
$ idris
     ____    __     _
    /  _/___/ /____(_)____
    / // __  / ___/ / ___/     Version 1.3.3
  _/ // /_/ / /  / (__  )      https://www.idris-lang.org/     
 /___/\__,_/_/  /_/____/       Type :? for help

Idris is free software with ABSOLUTELY NO WARRANTY.
For details type :warranty.
Idris> :l ch01/Hello.idr
*ch01/Hello> :exec
Hello, Idris World!
*ch01/Hello> :q  
Bye bye
```

- Idris 2
  - [Type Driven Development with Idris: Updates Required](https://idris2.readthedocs.io/en/latest/typedd/typedd.html)
```shell
✗ idris2
     ____    __     _         ___
    /  _/___/ /____(_)____   |__ \
    / // __  / ___/ / ___/   __/ /     Version 0.7.0-e0b9a027e
  _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org
 /___/\__,_/_/  /_/____/   /____/      Type :? for help

Welcome to Idris 2.  Enjoy yourself!
Main> :l "ch01/Hello.idr"
1/1: Building ch01.Hello (ch01/Hello.idr)
Loaded file ch01/Hello.idr
Main> main
MkIO (prim__putStr "Hello, Idris World!\n")
Main> :exec main
Hello, Idris World!
```
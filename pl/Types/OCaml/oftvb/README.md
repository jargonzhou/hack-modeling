# OCaml from the Very Beginning

- 3 `cases.ml`

```shell
$ ocaml
        OCaml version 4.08.1

# #use "cases.ml";;
val factorial : int -> int = <fun>
val isvowel : char -> bool = <fun>
val gcd : int -> int -> int = <fun>
# factorial 5;;
- : int = 120
# isvowel 'a';;
- : bool = true
# isvowel 'b';;
- : bool = false
# gcd 24 32;;
- : int = 8
# exit 0;;
```

- 4, 5 `lists.ml`

```shell
$ ocaml
        OCaml version 4.08.1

# #use "lists.ml";;
val length : 'a list -> int = <fun>
val append : 'a list -> 'a list -> 'a list = <fun>
val take : int -> 'a list -> 'a list = <fun>
val drop : int -> 'a list -> 'a list = <fun>
val sort : 'a list -> 'a list = <fun>
val msort : ('a -> 'a -> bool) -> 'a list -> 'a list = <fun>
# let l = [1;3;2;4;5];;      
val l : int list = [1; 3; 2; 4; 5]
# sort l;;
- : int list = [1; 2; 3; 4; 5]
# msort (fun x y -> x <= y) l;;
- : int list = [1; 2; 3; 4; 5]
# msort (fun x y -> x >= y) l;;
- : int list = [5; 4; 3; 2; 1]
# exit 0;;
```

- 6 `funs.ml`
```shell
$ ocamlc lists.ml funs.ml 
$ ./a.out 
6 5 4 2 1 
1 2 4 5 6 
```

- 7 `exceptions.ml`

```shell
$ ocaml exceptions.ml 
Division_by_zero
20
Problem
```

- 8 `dict.ml`

```shell
$ ocaml dict.ml 
{(1,one);(2,two)}
{(1,one);(2,two);(3,three)}
{(1,one);(2,two)}
{(1,one)}
false
one
```

- 9 `functions.ml`

```shell
$ ocaml functions.ml 
11
1; 2; 3
7; 8; 9
7; 8; 9
2; 4; 6
2; 4; 6
```

- 10 `types.ml`

```shell
$ ocaml types.ml
(255,0,0)
(255,0,0)
(0,255,0)
(255,255,0)
(150,0,255)
None
50
cake
7
```

- 11 `tree.ml`

```shell
$ ocamlc tree.ml treetest.ml
$ ./a.out 
tree: 
((((1,one)(((2,two)())(3,three)(((4,four)())
tree: 
(((((0,zero)()(1,one)(((2,two)())(3,three)(((4,four)())
```

- 12 `ios.ml`, `files.ml`

```shell
$ ocaml ios.ml 
$ ocamlc ios.mli ios.ml iostest.ml -o iotest
$ ./iotest 
100
1
one
1
one
2
two
3
three
1
one.
0
1
one.
```

```shell
$ ocamlc ios.mli ios.ml files.ml -o files
$ ./files
1
one
2
two
0
1
one
2
two
$ cat files.txt 
1
one
2
two
```

- 13 `boxes.ml`, `arraytest.ml`

```shell
$ ocaml boxes.ml 
0
0
0
50
```

```shell
$ ocaml arraytest.ml
[|1; 2; 3; 4; 5|]
Array.length a=5
a.(0)=1
[|1; 2; 3; 4; 100|]
[|true; true; true; true; true; true|]
[|A; A; A; A; A; A; A; A; A; A|]
[|[|5; 5; 5|]
; [|5; 5; 5|]
; [|5; 5; 5|]
|]
```

- 14 `floattest.ml`

```shell
$ ocaml floattest.ml 
1.5
6.
-2.3456
8.5
0.001
1e-05
5.9049e+34
0.123
1.79769313486e+308
2.22507385851e-308
(3., 4.)
5.
(0.1, 0.1)
(6., 8.)
```

- 15 `listtest.ml`

```shell
$ ocaml listtest.ml 
5
8
```

- 16 `stats.ml`, `textstat.mli`, `textstat.ml`

```shell
ocamlc textstat.ml
# #load "textstat.cmo";;
# let s = Textstat.stats_from_file "gregor.txt";;
# Textstat.lines s;;
# Textstat.characters s;;
# Textstat.words s;;
# Textstat.sentences s;;

$ ocamlc textstat.mli textstat.ml stats.ml -o stats
$ wc gregor.txt 
  7  85 468 gregor.txt
$ ./stats gregor.txt 
Words: 85
Characters: 469
Sentences: 4
Lines: 8
$ ./stats not_there.txt
An error occured: Sys_error("not_there.txt: No such file or directory")

ocamlopt textstat.mli textstat.ml stats.ml -o stats

```
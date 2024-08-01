# 17. Lexer and parser generators (ocamllex, ocamlyacc)

```shell
dune init proj lexer_parser
cd lexer_parser

dune build
dune exec lexer_parser
(1 + 2) * 3                         
9
1 + 2 * 3
7
^D
```
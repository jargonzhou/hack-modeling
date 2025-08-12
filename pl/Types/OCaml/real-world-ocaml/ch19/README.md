# 19 Parsing with OCamllex and Menhir


```shell
$ dune init proj ch19
$ cd ch19
```

- [lib/json.ml](./lib/json.ml): JSON helper
- [lib/lexer.mll](./lib/lexer.mll): `ocamllex` lexer
- [lib/parser.mly](./lib/parser.mly): Menhir parser

- [bin/main.ml](./bin/main.ml): entrypoint

- [test1.json](./test1.json), [test2.json](./test2.json): test files


```shell
$ dune build

$ dune exec ch19 test1.json
true                                
false
null
[1, 2, 3.000000, 4.000000, 0.500000, 550000.000000, 6.300000]
"Hello World"
{ "field1": "Hello",
  "field2": 170000000000000.000000,
  "field3": [1, 2, 3],
  "field4": { "fieldA": 1,
  "fieldB": "Hello" } }

$ dune exec ch19 test2.json
test2.json:3:2: syntax error 
```
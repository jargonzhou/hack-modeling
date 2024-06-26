# hello
- https://ocaml.org/docs/your-first-program

```shell
# WSL 2
# scaffolding project
$ opam exec -- dune init proj hello
Entering directory '/mnt/d/workspace/github/hack-modeling/Types/OCaml/hello'
Success: initialized project component named hello
$ tree hello/
hello/
├── _build
│   └── log
├── bin
│   ├── dune
│   └── main.ml
├── dune-project
├── hello.opam
├── lib
│   └── dune
└── test
    ├── dune
    └── test_hello.ml

4 directories, 8 files

# build project
$ cd hello
$ opam exec -- dune build

# execute
$ opam exec -- dune exec hello
Hello, World!

# add watch
$ opam exec -- dune build -w
$ opam exec -- dune exec hello -w

# utop
$ opam exec -- dune utop
utop # #show Hello.En;;
module En = Hello.En
module En : sig val v : string end

# use package modules
$ opam install sexplib
$ opam exec -- dune build
$ opam exec -- dune exec hello
Hello, World from en.ml!            
¡Hola, mundo!
(This(is an)(s expression))

# preprocessor
$ opam install ppx_show
$ opam exec -- dune build
$ opam exec -- dune exec hello
¡Hola, mundo!                       
(This(is an)(s expression))
["Hello"; "using"; "an"; "opam"; "library"]
```
# Code of 'Real World OCaml'

```shell
$ dune --version
3.16.0

$ opam install core core_bench utop
```

dune modes:

```
(modes byte exe)
```

utop session:

```shell
#utop_save "example.utop";;
```

Conventions:
- initialize project: `dune init proj chxx`.
- build and execute: `dune build`, `dune exec chxx`.
- inline test in `lib`.
  - Put `printf "Tests in %s" Stdlib.__FILE__;` in first test.
- alcotest test in `test`.
- utop session: `#utop_save "utop/<example-name>.utop";;`
- dune with utop: `dune utop`.

Contents:
- [1 A Guided Tour](./ch01/README.md)
- [2 Variables and Functions](./ch02/README.md)
- [4 Files, Modules, and Programs](./ch04/README.md)
- [5 Records](./ch05/README.md)
- [17 Testing](./ch17/README.md)
- [19 Parsing with OCamllex and Menhir](./ch19/README.md)
- [21 The OCaml Platform](./ch21/README.md)
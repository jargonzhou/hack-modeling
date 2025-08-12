# 4 Files, Modules, and Programs

```shell
dune build
grep -Eo '[[:alpha:]]+' lib/freq.ml | dune exec ch04 
```

- [freq.ml](./lib/freq.ml), [counter.mli](./lib/counter.mli), [counter.ml](./lib/counter.ml): multifile program
- [abstract_username.ml](./lib/abstract_username.ml), [](./lib/session_info.ml): nested module
- [abstract_interval.ml](./lib/abstract_interval.ml): including module
- [ext_option.mli](./lib/ext_option.mli), [ext_option.ml](./lib/ext_option.ml), [import.ml](./lib/import.ml), [test_ch04.ml](./test/test_ch04.ml): includeing module, replace `Option` module.
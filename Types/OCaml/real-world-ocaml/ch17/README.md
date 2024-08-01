# 17 Testing

```shell
$ opam install patdiff

$ dune init proj ch17
$ cd ch17
$ dune runtest
```

## Inline Tests

`test`:

```shell
File "lib/test.ml", line 3, characters 0-138: rev is false.

FAILED 1 / 1 tests
```

`test_eq`:

```shell
File "lib/test_eq.ml", line 4, characters 0-79: rev threw
(runtime-lib/runtime.ml.E "comparison failed"
  ((1 2 3) vs (3 2 1) (Loc lib/test_eq.ml:5:13))).
  Raised at Ppx_assert_lib__Runtime.test_eq in file "runtime-lib/runtime.ml", line 91, characters 22-69
  Called from Ch17__Test_eq.(fun) in file "lib/test_eq.ml", line 5, characters 13-21

FAILED 1 / 1 tests
```

## Expect Tests

`expect_test`:

```shell
File "lib/test_expect.ml", line 1, characters 0-0:
------ lib/test_expect.ml
++++++ lib/test_expect.ml.corrected
File "lib/test_expect.ml", line 12, characters 0-1:
 |open! Base
 |open Stdio
 |
 |let%expect_test "trivial" =
 |  print_endline "Hello World!";
 |  [%expect {| Hello World! |}]
 |
 |let%expect_test "multi-block" =
 |  print_endline "Hello";
 |  [%expect {| Hello |}];
 |  print_endline "World!";
-|  [%expect {| World!! |}]
+|  [%expect {| World! |}]
No newline at the end of lib/test_expect.ml
No newline at the end of lib/test_expect.ml.corrected
```

with `sexp`:

```shell
-|  [%expect {| (3 2 1) |}]
+|  [%expect {| (1 2 3) |}]
```

## Property Testing with Quickcheck

## Other Testing Tools

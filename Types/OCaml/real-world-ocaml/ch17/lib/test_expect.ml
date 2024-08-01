open! Base
open Stdio

let%expect_test "trivial" =
  print_endline "Hello World!";
  [%expect {| Hello World! |}]

let%expect_test "multi-block" =
  print_endline "Hello";
  [%expect {| Hello |}];
  print_endline "World!";
  [%expect {| World! |}]

(* #require "ppx_jane";; *)
let%expect_test _ =
  print_s [%sexp (List.rev [ 3; 2; 1 ] : int list)];
  (* [%expect {| (3 2 1) |}] *)
  [%expect {| (1 2 3) |}]
open Base
open Stdio

let square x = x * x

let%test_unit "square" =
  printf "Tests in %s" Stdlib.__FILE__;
  [%test_eq: int] (square 2) 4;
  [%test_eq: int] (square (square 2)) 16

let ratio x y = Float.of_int x /. Float.of_int y

let ratio2 x y =
  (* Float.O.(of_int x / of_int y) *)
  let open Float.O in
  of_int x / of_int y

let%test "ratio" =
  (* printf "%.30F\n" (ratio 4 7); *)
  Float.equal (ratio 4 7) 0.571428571428571396850770724996

let%test "ratio2" = Float.equal (ratio2 4 7) 0.571428571428571396850770724996

let sum_if_true (test : int -> bool) (first : int) (second : int) : int =
  (if test first then first else 0) + if test second then second else 0

let even x = x % 2 = 0

let%test_unit "even" =
  [%test_eq: int] (sum_if_true even 3 4) 4;
  [%test_eq: int] (sum_if_true even 2 4) 6

(******************************************************************************
  interring generic types
  ******************************************************************************)
let first_if_ture test x y = if test x then x else y
let long_string s = String.length s > 6

let%test "first_if_true long_string" =
  String.equal
    (first_if_ture long_string "short" "looooooooooong")
    "looooooooooong"

let big_number x = x > 3
let%test "first_if_true big_number" = Int.equal (first_if_ture big_number 4 3) 4

(* let%test "first_if_true failed" =
   String.equal (first_if_ture big_number "short" "looooooooooong") "looooooooooong" *)

(******************************************************************************
  type errors v.s. exceptions
  ******************************************************************************)
(* let add_potato x = x + "potato" *)

let is_a_multiple x y = x % y = 0

let%test_unit "is_a_multiple" =
  [%test_eq: bool] (is_a_multiple 8 2) true;
  [%test_eq: bool]
    (try
       let a = is_a_multiple 8 0 in
       a
     with Invalid_argument _ -> false)
    false

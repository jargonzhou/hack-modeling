open Base
open Stdio

(******************************************************************************
Anonymous functions
******************************************************************************)
let%test_unit "anonymous functions" = 
  printf "Tests in %s" Stdlib.__FILE__;
  [%test_eq: int] ((fun x -> x + 1) 7) 8;
  [%test_eq: int list] (List.map ~f:(fun x -> x + 1) [1;2;3]) [2;3;4];
  let transforms = [String.uppercase; String.lowercase] in
  [%test_eq: string list] (List.map ~f:(fun g -> g "Hello World") transforms)
    ["HELLO WORLD"; "hello world"];
  let plusone x = x + 1 in
    [%test_eq: int] (plusone 1) 2

(******************************************************************************
Multiargument functions
******************************************************************************)
let abs_diff x y = abs (x - y)

let%test_unit "abs_diff" = 
  [%test_eq: int] (abs_diff 3 4) 1;
  let dist_from_3 = abs_diff 3 in (* partial application *)
    [%test_eq: int] (dist_from_3 8) 5;
    [%test_eq: int] (dist_from_3 (-1)) 4

(* tuple argument *)
let%test_unit "tuple argument" = 
  let abs_diff (x,y) = abs (x - y) in
  [%test_eq: int] (abs_diff (3,4)) 1

(******************************************************************************
Recursive functions
******************************************************************************)
let rec find_first_repeat list =
  match list with
  | [] | [_] -> None
  | x :: y :: tl -> 
    if x = y then Some x else find_first_repeat (y :: tl)

(* mutually recursive *)
let rec is_even x =
  if x = 0 then true else is_odd (x - 1)
and is_odd x = 
  if x = 0 then false else is_even (x - 1)

let%test_unit "is_even, is_odd" = 
  [%test_eq: bool list] (List.map ~f:is_even [0;1;2;3;4;5]) [true;false;true;false;true;false];
  [%test_eq: bool list] (List.map ~f:is_odd [0;1;2;3;4;5]) [false;true;false;true;false;true]

(******************************************************************************
Prefix and Infix Operators
******************************************************************************)

let%test_unit "operator" = 
  let (+!) (x1, y1) (x2, y2) = (x1 + x2, y1 + y2) in
  [%test_eq: int * int] ((3,2) +! (-2,4)) (1,6);
  let ( *** ) x y = (x **. y) **. y in
    [%test_eq: float] (2. *** 3. ) 512.

(* reverse application operator *)
let%expect_test "|>" = 
  let path = "/usr/bin:/usr/local/bin:/bin:/sbin:/usr/bin" in
  String.split ~on:':' path
  |> List.dedup_and_sort ~compare:String.compare
  |> List.iter ~f:print_endline;
  [%expect {|/bin
/sbin
/usr/bin
/usr/local/bin|}]

(* application operator: (@@) *)

(******************************************************************************
Declaring functions with `function`
******************************************************************************)
let some_or_zero = function
| Some x -> x
| None -> 0

let%test_unit "some_or_zero" = 
  [%test_eq: int list] (List.map ~f:some_or_zero [Some 3; None; Some 4]) [3;0;4]

let some_or_default default = function
| Some x -> x
| None -> default

let%test_unit "some_or_default" = 
  [%test_eq: int] (some_or_default 3 (Some 5)) 5; 
  [%test_eq: int list] (List.map ~f:(some_or_default 100) [Some 3; None; Some 4]) [3;100;4]

(******************************************************************************
Labeled arguments
******************************************************************************)

(******************************************************************************
Optional arguments
******************************************************************************)




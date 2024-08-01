open Base
open Stdio

(******************************************************************************
  Arrays
  ******************************************************************************)

let%test_unit "arrays" =
  printf "Tests in %s" Stdlib.__FILE__;
  let numbers = [| 1; 2; 3; 4 |] in
  [%test_eq: unit] (numbers.(2) <- 4) ();
  [%test_eq: int array] numbers [| 1; 2; 4; 4 |]

(******************************************************************************
  Mutable Record Fields
  ******************************************************************************)
type running_sum = {
  mutable sum : float;
  mutable sum_sq : float; (* sum of squares *)
  mutable samples : int;
}

let mean rsum = rsum.sum /. Float.of_int rsum.samples

let stdev rsum =
  Float.sqrt ((rsum.sum_sq /. Float.of_int rsum.samples) -. (mean rsum **. 2.))

let create () = { sum = 0.; sum_sq = 0.; samples = 0 }

let update rsum x =
  rsum.samples <- rsum.samples + 1;
  rsum.sum <- rsum.sum +. x;
  rsum.sum_sq <- rsum.sum_sq +. (x *. x)

let%test_unit "running_sum" =
  let rsum = create () in
  List.iter [ 1.; 3.; 2.; -7.; 4.; 5. ] ~f:(fun x -> update rsum x);
  [%test_eq: float] (mean rsum) 1.33333333333333326;
  [%test_eq: float] (stdev rsum) 3.94405318873307698

(******************************************************************************
  Refs
  ******************************************************************************)

let sum list =
  let sum = ref 0 in
  List.iter list ~f:(fun x -> sum := !sum + x);
  !sum

let%test_unit "sum using ref" = [%test_eq: int] (sum [ 1; 2; 3; 4; 5 ]) 15

(******************************************************************************
  For and while loop
  ******************************************************************************)
let permute array =
  let length = Array.length array in
  for i = 0 to length - 2 do
    (* Pick j to swap *)
    let j = i + Random.int (length - i) in
    (* Swap i,j *)
    let tmp = array.(i) in
    array.(i) <- array.(j);
    array.(j) <- tmp
  done

let%test_unit "permute" =
  let ar = Array.init 20 ~f:(fun i -> i) in
  permute ar;
  Stdlib.print_newline ();
  Array.iter ar ~f:(fun x ->
      Stdlib.print_int x;
      Stdlib.print_char ' ');
  [%test_eq: int] (Array.length ar) 20

let find_first_negative_entry array =
  let pos = ref 0 in
  while !pos < Array.length array && array.(!pos) >= 0 do
    pos := !pos + 1
  done;
  if !pos = Array.length array then None else Some !pos

let%test_unit "find_first_negative_entry" =
  [%test_eq: int option] (find_first_negative_entry [| 1; 2; 0; 3 |]) None;
  [%test_eq: int option] (find_first_negative_entry [| 1; -2; 0; 3 |]) (Some 1)

open Base
open Stdio

(******************************************************************************
Varaibles
******************************************************************************)

let%test_unit "languages" = 
  printf "Tests in %s" Stdlib.__FILE__;
  let languages = "OCaml,Perl,C++,C" in
  let language_list = String.split ~on:',' languages in
  let dashed_language = String.concat ~sep:"-" language_list in
  [%test_eq: string] dashed_language "OCaml-Perl-C++-C"

let area_of_ring inner_radius outer_radius =
  let pi = Float.pi in
  let area_of_circle r = pi *. r *. r in
  area_of_circle outer_radius -. area_of_circle inner_radius

let%test_unit "area_of_ring" = 
  [%test_eq: float] (area_of_ring 1. 3.) 25.132741228718345

(******************************************************************************
Pattern match and let
******************************************************************************)
let%test_unit "pattern match and let" = 
  let (ints, strings) = List.unzip [(1,"one"); (2, "two"); (3, "three")] in
  [%test_eq: int list] ints [1;2;3];
  [%test_eq: string list] strings ["one";"two";"three"]

let upcase_first_entry line =
  match String.split ~on:',' line with
  | [] -> assert false (* cannot happend: String.split returns at least one element*)
  | first :: rest -> String.concat ~sep:"," (String.uppercase first :: rest)

let%test_unit "upcase_first_entry" = 
  [%test_eq: string] (upcase_first_entry "one,two,three") "ONE,two,three";
  [%test_eq: string] (upcase_first_entry "") ""
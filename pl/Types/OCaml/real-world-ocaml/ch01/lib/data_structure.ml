open Base
open Stdio

(******************************************************************************
  Tuples
  ******************************************************************************)

let a_tuple = (3, "three")
let another_tuple = (3, "four", 5.)

let%test_unit "tuple pattern match" =
  printf "Tests in %s" Stdlib.__FILE__;
  let x, y = a_tuple in
  [%test_eq: int] x 3;
  [%test_eq: string] y "three";
  [%test_eq: int] (x + String.length y) 8

let distance (x1, y1) (x2, y2) =
  Float.sqrt (((x1 -. x2) **. 2.) +. ((y1 -. y2) **. 2.))

(******************************************************************************
  Lists
  ******************************************************************************)
let languages = [ "OCaml"; "Perl"; "C" ]

let%test_unit "list module" =
  [%test_eq: int] (List.length languages) 3;
  [%test_eq: int list] (List.map languages ~f:String.length) [ 5; 4; 1 ]

let%test_unit "constructing list with ::" =
  [%test_eq: string list]
    ("French" :: "Spanish" :: languages)
    [ "French"; "Spanish"; "OCaml"; "Perl"; "C" ];
  [%test_eq: string list] languages [ "OCaml"; "Perl"; "C" ]

let a = (1, 2, 3)
let b = [ 1; 2; 3 ]
let c = [ 1; 2; 3 ]
let d = [ 1; 2; 3 ] @ [ 4; 5; 6 ]

let my_favirote_language languages =
  match languages with first :: _ -> first | [] -> "OCaml"

let%test_unit "my_favirote_language" =
  [%test_eq: string]
    (my_favirote_language [ "English"; "Spanlist"; "French" ])
    "English";
  [%test_eq: string] (my_favirote_language []) "OCaml"

(******************************************************************************
  recursive list functions
  ******************************************************************************)
let rec sum l = match l with [] -> 0 | hd :: tl -> hd + sum tl
let%test_unit "sum" = [%test_eq: int] (sum [ 1; 2; 3 ]) 6

let rec remove_sequential_duplicates list =
  match list with
  | [] -> []
  | [ x ] -> [ x ]
  | first :: second :: tl ->
      if first = second then remove_sequential_duplicates (second :: tl)
      else first :: remove_sequential_duplicates (second :: tl)

let%test_unit "remove_sequence_duplicates" =
  [%test_eq: int list]
    (remove_sequential_duplicates [ 1; 1; 2; 3; 3; 4; 4; 1; 1; 1 ])
    [ 1; 2; 3; 4; 1 ]

(******************************************************************************
  Options
  ******************************************************************************)
let divide x y = if y = 0 then None else Some (x / y)

let downcase_extension filename =
  match String.rsplit2 filename ~on:'.' with
  | None -> filename
  | Some (base, ext) -> base ^ "." ^ String.lowercase ext

let%test_unit "downcase_extension" =
  [%test_eq: string list]
    (List.map ~f:downcase_extension
       [ "Hello_World.TXT"; "Hello_World.txt"; "Hello_World" ])
    [ "Hello_World.txt"; "Hello_World.txt"; "Hello_World" ]

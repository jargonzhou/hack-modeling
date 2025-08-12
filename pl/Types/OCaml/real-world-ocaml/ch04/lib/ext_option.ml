open Base
open Stdio

(* include the full content of option module. *)
include Option

let apply f_opt x = 
  printf "apply in %s" Stdlib.__FILE__;
  match f_opt with None -> None | Some f -> Some (f x)

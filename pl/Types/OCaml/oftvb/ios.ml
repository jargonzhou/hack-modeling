let print_dict_entry (k,v) =
  print_int k;
  print_newline ();
  print_string v;
  print_newline ();;

(* let rec print_dict d =
  match d with
    [] -> ()
  | h::t -> print_dict_entry h; print_dict t;; *)

let rec iter f l =
  match l with
    [] -> ()
  | h::t -> f h; iter f t;;

let print_dict =
  iter print_dict_entry;;

let rec read_dict () =
  try
    let i = read_int () in
    if i = 0 
    then []
    else 
      let name = read_line () in
        (i, name) :: read_dict ();
  with
    Failure _ ->
      print_string "This is not a valid integer. Please try again";
      print_newline ();
      read_dict ();;


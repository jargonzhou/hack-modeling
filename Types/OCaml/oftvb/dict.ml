let rec lookup k d =
  match d with
  | [] -> raise Not_found
  | (k',v)::t -> if k = k' then v else lookup k t;;

let rec add k v d =
  match d with
  | [] -> [(k,v)]
  | (k',v')::t -> 
      if k = k' 
      then (k,v) :: t 
      else (k',v') :: add k v t;;

let rec remove k d =
  match d with
  | [] -> []
  | (k',v')::t ->
      if k = k'
      then t
    else (k',v') :: remove k t;;

let key_exists k d =
  try
    let _ = lookup k d in true
  with
    Not_found -> false;;

let dump d fk fv =
  let rec dodump d fk fv =
    let print_kv (k,v) =
      print_string "("; fk k; print_char ','; fv v; print_string ")"
    in 
      match d with
      | [] -> ()
      | h::[] -> print_kv h
      | h::t -> print_kv h; print_string ";"; dodump t fk fv
  in
    print_string "{";
    dodump d fk fv;
    print_string "}\n";;

let () =
  let d = [(1, "one"); (2, "two")] 
  and fk = print_int
  and fv = print_string
  in
    dump d fk fv;
    dump (add 3 "three" d) fk fv;
    dump d fk fv;

    dump (remove 2 d) fk fv;

   print_string ( string_of_bool (key_exists 4 d));
   print_newline ();

   try
    let v = lookup 1 d in
      print_string v; print_newline ();
   with
    Not_found -> print_string "not found";
let add x y = x + y;;
let add2 = fun x -> fun y -> x + y;;

let rec mapl f ll = 
  match ll with
| [] -> []
| h::t -> List.map f h :: mapl f t;;

let mapl2 f = List.map (List.map f);;

let () =
  (* partitial application *)
  let ff = add 6 in
    print_int (ff 5); print_newline ();
  let rec print_list f = function
    [] -> ()
    | h::[] -> f h;
    | h::t -> f h; print_string "; "; print_list f t;
  in
    let l = [1;2;3] in
      print_list print_int l; print_newline ();

      print_list print_int (List.map (add 6) l); print_newline ();
      print_list print_int (List.map (add2 6) l); print_newline ();

      print_list print_int (List.map (fun x -> x * 2) l); print_newline ();
      print_list print_int (List.map (( * ) 2) l); print_newline ();
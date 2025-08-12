(* Usage of standard libaray module List *)

let () = 
  let list = [1;2;3;4;5] in
    print_int (List.length list); print_newline ();
  let list2 = [1;2;4;8;15;3] in
    print_int (List.nth list2 3); print_newline ();
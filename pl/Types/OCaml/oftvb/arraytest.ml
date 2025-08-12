let print_array f a = 
  let rec print_list = function
    [] -> ()
    | h::[] -> f h;
    | h::t -> f h; print_string "; "; print_list t;
  in
    print_string "[|";
    print_list (Array.to_list a);
    print_string "|]";
    print_newline ();; (* note ;; here*)

let () = 
  let a = [|1;2;3;4;5|] in
    print_array print_int a;
    print_string "Array.length a="; print_int (Array.length a); print_newline ();
    print_string "a.(0)="; print_int a.(0); print_newline ();    
    a.(4) <- 100;
    print_array print_int a;

  let a2 = Array.make 6 true in
    print_array (fun x -> print_string (string_of_bool x)) a2;
  
  let a3 = Array.make 10 'A' in
    print_array print_char a3;
  
  let aa = Array.make 3 (Array.make 3 5) in
    print_array (fun a -> print_array (print_int) a) aa
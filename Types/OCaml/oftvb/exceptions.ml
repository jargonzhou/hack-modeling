exception Problem
exception NotPrime of int

let rec take n l =
  match l with
  | [] -> if n = 0 then [] else raise (Invalid_argument "take")
  | h::t -> if n < 0 then raise (Invalid_argument "take") 
            else if n = 0 then [] else h :: take (n-1) t

let rec drop n l =
  match l with
  | [] -> if n = 0 then [] else raise (Invalid_argument "drop")
  | h::t -> if n < 0 then raise (Invalid_argument "drop") else
              if n = 0 then l else drop (n-1) t

let safe_divice x y =
  try x / y with
  Division_by_zero -> 0

let rec last l = match l with
| [] -> raise Not_found
| [x] -> x
| _::t -> last t

let () =
  try
    print_int (10 / 0);
  with
    e -> print_string (Printexc.to_string e); print_newline ();
  
  let f x = if x < 0 then raise Problem else 100 / x in
    print_int (f 5); print_newline ();
    try 
      print_int (f (-1));
    with
      e -> print_string (Printexc.to_string e); print_newline ();
  
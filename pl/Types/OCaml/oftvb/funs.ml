let rec double l = 
  match l with
  | [] -> []
  | h::t -> (h * 2) :: double t

let rec evens l =
  match l with
  | [] -> []
  | h::t -> (h mod 2 = 0) :: evens t

let rec map f l =
  match l with
  | [] -> []
  | h::t -> f h :: map f t

let halve x = x / 2

let is_even x = 0
let evens2 l = map is_even l
let evens3 l = map (fun x -> x mod 2 = 0) l

let greater a b = a >= b



let () =
  List.iter (fun x -> print_int x; print_char ' ') (Lists.msort greater [5; 4; 6; 2; 1]);
  print_newline ();

  List.iter (fun x -> print_int x; print_char ' ') (Lists.msort (fun x y -> x <= y) [5; 4; 6; 2; 1]);
  print_newline ();

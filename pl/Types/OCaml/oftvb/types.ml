type colour =
  Red
| Green
| Blue
| Yellow
| RGB of int * int * int;;

let components c =
  match c with
    Red -> (255, 0,0)
  | Green -> (0, 255, 0)
  | Blue -> (0, 0, 255)
  | Yellow -> (255, 255, 0)
  | RGB (r,g,b) -> (r,g,b);;

let print_colour c =
  let (r,g,b) = components c in
    print_string "(";
    print_int r; print_char ',';
    print_int g; print_char ',';
    print_int b;
    print_string ")\n";;

let print_option o f =
  match o with
  | None -> print_string "None"
  | Some x -> f x;;

let rec print_list f l= 
  match l with
    [] -> ()
  | h::t -> f h; print_list f t;;

let rec lookup_option x l =
  match l with
  | [] -> None
  | (k,v)::t -> if x = k then Some v else lookup_option x t;;

(* Recursive types *)
type 'a sequence =
  Nil
| Cons of 'a * 'a sequence;;

let rec length s =
  match s with
  | Nil -> 0
  | Cons(_, t) -> 1 + length t;;

let rec append s1 s2 =
  match s1 with
  | Nil -> s2
  | Cons(h,t) -> Cons(h, append t s2);;

(* Type of math expression *)
type expr =
  Num of int
| Add of expr * expr
| Subtract of expr * expr
| Multiply of expr * expr
| Divice of expr * expr;;

let rec evaluate expr = match expr with
  Num(v) -> v
| Add(e1,e2) -> evaluate e1 + evaluate e2
| Subtract(e1,e2) -> evaluate e1 - evaluate e2
| Multiply(e1, e2) -> evaluate e1 * evaluate e2
| Divice(e1, e2) -> evaluate e1 / evaluate e2;;

let () =
  let cols = [Red; Red; Green; Yellow; RGB (150, 0, 255)] in
    List.iter print_colour cols;;
  
  let nothing = None
  and number = Some 50
  (* and numbers = [Some 12; None; None; Some 2] *)
  and word = Some ['c';'a';'k';'e'] in
    print_option nothing print_string;
    print_newline ();
    print_option number print_int;
    print_newline ();
    match word with
      None -> ()
    | Some v -> print_list print_char v;
    print_newline ();

  (* 1 + 2 * 3 *)
  let expr = Add (Num 1, Multiply (Num 2, Num 3)) in
    print_int (evaluate expr);
    print_newline ();

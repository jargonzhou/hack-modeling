type 'a tree =
  Br of 'a * 'a tree * 'a tree (* branch *)
| Lf (* leaf *)

let rec size tr =
  match tr with
    Br (_,l,r) -> 1 + size l + size r
  | Lf -> 0;;

let rec total tr =
  match tr with
    Br (x, l, r) -> x + total l + total r
  | Lf -> 0;;

let max x y = if x > y then x else y;;

let rec maxdepth tr =
  match tr with
    Br (_, l, r) -> 1 + max (maxdepth l) (maxdepth r)
  | Lf -> 0;;

let rec list_of_tree tr =
  match tr with
    Br (x,l,r) -> list_of_tree l @ [x] @ list_of_tree r
  | Lf -> [];;

let rec tree_map f tr =
  match tr with
    Br (x,l,r) -> Br (f x, tree_map f l, tree_map f r)
  | Lf -> Lf;;

let rec lookup tr k =
  match tr with
    (* Lf -> raise Not_found *)
    Lf -> None
  | Br ((k', v), l, r) ->
      (* if k = k' then v *)
      if k = k' then Some v
      else if k < k' then lookup l k
      else lookup r k;;

let rec insert tr k v =
  match tr with
    Lf -> Br ((k,v), Lf, Lf)
  | Br ((k',v'), l, r) ->
      if k = k' then Br ((k,v), l, r)
      else if k < k' then Br ((k', v'), insert l k v, r)
      else Br ((k', v'), l, insert r k v);;

let rec print_tree tr fk fv =
  print_string "(";
  match tr with
    Lf -> ()
  | Br ((k,v), l, r) -> 
      print_tree l fk fv; 
      print_string "(";
      fk k; 
      print_string ",";
      fv v; 
      print_string ")";
      print_tree r fk fv;
  print_string ")";;

let rec length l =
  match l with
  | [] -> 0
  | h::t -> 1 + length t

let rec append a b =
  match a with
  |[] -> b
  | h::t -> h :: append t b

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


(* Insertion sort *)
let rec sort l = 
  let rec insert x l =
    match l with
    | [] -> [x]
    | h::t -> if x <= h then x :: h :: t else h :: insert x t
  in
    match l with
    | [] -> []
    | h::t -> insert h (sort t)

(* Merge sort *)
let rec msort fcmp l =
  let rec merge fcmp x y =
    match x,y with
    | [], l -> l
    | l, [] -> l
    | hx::tx, hy::ty ->
        if fcmp hx hy
        then hx :: merge fcmp tx (hy :: ty)
        else hy :: merge fcmp (hx :: tx) ty
  in 
    match l with
    | [] -> []
    | [x] -> [x]
    | _ -> let left = take (length l / 2) l in
                let right = drop (length l / 2) l in
                  merge fcmp (msort fcmp left) (msort fcmp right)
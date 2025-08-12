let rec factorial a =
  match a with
  | 1 -> 1
  | _ -> a * factorial (a - 1)

let isvowel c =
  match c with
  | 'a' | 'e' |'i'|'o'|'u' -> true
  | _ -> false

let rec gcd a b =
  match b with
  | 0 -> a 
  | _ -> gcd b (a mod b)


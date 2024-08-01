open Base
open Ch04.Import

let lookup_and_apply map key x 
= Option.apply (Map.find map key) x

let () = 
  let map =  Map.empty (module String) in
    let _ = lookup_and_apply map "" 1 in
      assert (1 = 1)

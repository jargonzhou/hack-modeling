open Base

let%test_unit "rev" =
  (* [%test_eq: int list] (List.rev [ 3; 2; 1 ]) [ 3; 2; 1 ] *)
  [%test_eq: int list] (List.rev [ 3; 2; 1 ]) [ 1; 2; 3 ]
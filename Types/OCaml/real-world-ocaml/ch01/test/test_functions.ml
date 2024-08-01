open Ch01.Functions

let test_quare () =
  Alcotest.(check int) "same int" 4 (square 2);
  Alcotest.(check int) "same int" 16 (square (square 2))

let test_check_raises () =
  (* check_raises *)
  Alcotest.check_raises "/ 0"
    (Invalid_argument "8 % 0 in core_int.ml: modulus should be positive")
    (fun () ->
      let _ = is_a_multiple 8 0 in
      ())

let () =
  let open Alcotest in
  run "Functions"
    [
      ("square", [ test_case "square" `Quick test_quare ]);
      ("is_a_multiple", [ test_case "exception" `Quick test_check_raises ]);
    ]

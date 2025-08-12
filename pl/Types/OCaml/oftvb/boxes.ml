
let swap a b =
  let t = !a in
    a := !b; b := t

(* while loop*)
let smallest_pow2 x = 
    let t = ref 1 in
      while !t < x do
        t := !t * 2
      done;
      !t

let () = 
  print_string "ref:\n";
  let x = ref 0 in
    print_int !x; print_newline ();
    let p = !x in
      print_int p; print_newline ();
      x := 50;
      print_int p; print_newline ();
      let q = !x in
      print_int q; print_newline ();

  print_string "swap:\n";
  let a = ref 1 in
    let b = ref 2 in
      print_int !a; print_char ' '; print_int !b;
      print_newline ();
      swap a b;
      print_int !a; print_char ' '; print_int !b;
      print_newline ();

  print_string "begin ... end:\n";
  let a = ref 0 in
    let b = ref 0 in
      let x = 0 in
        let y = 0 in
          if x = y then
            begin
              a := !a + 1;
              b := !b - 1
            end
          else
            (a := !a - 1; b := !b + 1);
          print_int !a; print_char ' '; print_int !b;
          print_newline ();

  (* for loop *)
  print_string "for loop:\n";
  for x = 1 to 5 do
    print_int x;
    print_newline ();
  done;

  print_string "while loop:\n";
  print_int (smallest_pow2 64);
  print_newline (); 
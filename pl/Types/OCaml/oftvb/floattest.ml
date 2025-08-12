let make_vector (x0,y0) (x1,y1) =
  (x1 -. x0, y1 -. y0)

let string_of_vector (x,y) =
  "(" ^ string_of_float x ^ ", " ^ string_of_float y ^ ")"

let vector_length (x, y) =
  sqrt (x *. x +. y *. y)

let offset_point (x,y) (px, py) = 
  (px +. x, py +. y)

let scale_to_length l (a,b) =
  let currentlength = vector_length (a,b) in
    if currentlength == 0.
    then (a, b)
    else
      let factor = l /. currentlength in
        (a *. factor, b *. factor)

let () =
  print_float 1.5; print_newline ();
  print_float 6.; print_newline ();
  print_float (-.2.3456); print_newline ();
  print_float (1.0 +. 2.5 *. 3.0); print_newline ();
  print_float (1.0 /. 1000.0); print_newline ();
  print_float (1. /. 100000.); print_newline ();
  print_float (3000. ** 10.); print_newline ();
  print_float (3.123 -. 3.); print_newline ();

  print_float max_float; print_newline ();
  print_float min_float; print_newline ();

  let v = make_vector (0.,0.) (3.,4.) in
      print_string (string_of_vector v); print_newline ();
      print_float (vector_length v); print_newline ();
      let offset = offset_point (0.,0.) (0.1,0.1) in
        print_string (string_of_vector offset); print_newline ();
      print_string (string_of_vector (scale_to_length 10. v)); print_newline ();

  

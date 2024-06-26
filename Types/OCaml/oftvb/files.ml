let entry_to_channel ch (k,v) =
  output_string ch (string_of_int k);
  output_char ch '\n';
  output_string ch v;
  output_char ch '\n';;

let dictionary_to_channel ch d =
  let rec iter f l =
    match l with
      [] -> ()
    | h::t -> f h; iter f t
  in
    iter (entry_to_channel ch) d;;

let dictionary_to_file filename dict =
  let ch = open_out filename in
    dictionary_to_channel ch dict;
    close_out ch;;

let entry_of_channel ch =
  let number = input_line ch
  and name = input_line ch in
    (int_of_string number, name);;

let rec dictionary_of_channel ch =
  try
    let e = entry_of_channel ch in
      e :: dictionary_of_channel ch
  with
    End_of_file -> [];;

let dictionary_of_file filename =
  let ch = open_in filename in
    let dict = dictionary_of_channel ch in
      close_in ch;
      dict;;

let () =
  dictionary_to_file "files.txt" (Ios.read_dict ());
  let d = dictionary_of_file "files.txt" in
    Ios.print_dict d;
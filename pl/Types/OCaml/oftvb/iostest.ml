let () =
  print_int 100;
  print_newline ();

  Ios.print_dict_entry (1, "one");

  Ios.print_dict [(1,"one"); (2, "two"); (3, "three")];

  let d = Ios.read_dict () in
    Ios.print_dict d;
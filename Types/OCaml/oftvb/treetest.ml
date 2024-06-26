let tr = Tree.Br ((3, "three"), Br ((1, "one"), Lf, Br ((2, "two"), Lf, Lf)), Br ((4, "four"), Lf, Lf)) 
in
  print_string "tree: \n";
  (* Ios.print_dict (Tree.list_of_tree tr); *)
  Tree.print_tree tr print_int print_string;
  print_newline ();

  let tr = Tree.insert tr 0 "zero" in
    print_string "tree: \n";
    (* Ios.print_dict (Tree.list_of_tree tr); *)
    Tree.print_tree tr print_int print_string;
    print_newline ();
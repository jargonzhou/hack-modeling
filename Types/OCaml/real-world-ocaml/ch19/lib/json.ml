type value =
  [ `Assoc of (string * value) list
  | `Bool of bool
  | `Float of float
  | `Int of int
  | `List of value list
  | `Null
  | `String of string ]


let rec output_value outc = function
  | `Assoc obj -> print_assoc outc obj
  | `List l -> print_list outc l
  | `String s -> Core.printf "\"%s\"" s
  | `Int i -> Core.printf "%d" i
  | `Float x -> Core.printf "%f" x
  | `Bool true -> output_string outc "true"
  | `Bool false -> output_string outc "false"
  | `Null -> output_string outc "null"

and print_assoc outc obj =
  output_string outc "{ ";
  let sep = ref "" in
  Core.List.iter
    ~f:(fun (key, value) ->
      Core.printf "%s\"%s\": %a" !sep key output_value value;
      sep := ",\n  ")
    obj;
  output_string outc " }"

and print_list outc arr =
  output_string outc "[";
  Core.List.iteri
    ~f:(fun i v ->
      if i > 0 then output_string outc ", ";
      output_value outc v)
    arr;
  output_string outc "]"

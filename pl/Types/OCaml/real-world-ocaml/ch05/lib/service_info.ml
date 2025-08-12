(******************************************************************************
  Service info in /etc/services.
  ******************************************************************************)
open Base
open Stdio

type service_info = {
  service_name : string;
  port : int;
  protocol : string;
  comment : string option;
}

let service_info_of_string line =
  let matches =
    let pat = "([a-zA-Z\\-]+)[ \t]+([0-9]+)/([a-zA-Z]+)[ \t]+#[ \t]+(.+)" in
    Re.exec (Re.Posix.compile_pat pat) line
  in
  {
    service_name = Re.Group.get matches 1;
    port = Int.of_string (Re.Group.get matches 2);
    protocol = Re.Group.get matches 3;
    comment = Re.Group.get_opt matches 4;
  }

let%test_unit "service_info_of_string" =
  printf "Tests in %s" Stdlib.__FILE__;
  let line = "ssh 22/udp # SSH Remote Login Protocol" in
  let r = service_info_of_string line in
  (* can we test record equality??? *)
  [%test_eq: string] r.service_name "ssh";
  [%test_eq: int] r.port 22;
  [%test_eq: string] r.protocol "udp";
  [%test_eq: string option] r.comment (Some "SSH Remote Login Protocol")

type 'a with_line_num = { item : 'a; line_num : int }
(** An arbitrary item tagged with a line number.  *)

let parse_lines parse file_contents =
  let lines = String.split ~on:'\n' file_contents in
  List.mapi lines ~f:(fun line_num line ->
      { item = parse line; line_num = line_num + 1 })

(* field punning *)
let service_info_to_string { service_name ; port; protocol; comment } =
  let base = Printf.sprintf "%s %i/%s" service_name port protocol in
  match comment with
  | None -> base
  | Some text -> base ^ " # " ^ text

let%test_unit "service_info_to_string" =
  let ssh = service_info_of_string "ssh 22/udp # SSH Remote Login Protocol" in
  [%test_eq: string] (service_info_to_string ssh) "ssh 22/udp # SSH Remote Login Protocol"


let create_service_info ~service_name ~port ~protocol ~comment =
  {service_name; port; protocol; comment}
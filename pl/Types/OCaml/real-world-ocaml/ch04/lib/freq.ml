(******************************************************************************
  Read line from stdin, compute frequency count of the line.
  ******************************************************************************)
open Stdio

let build_counts () =
  In_channel.fold_lines In_channel.stdin ~init:Counter.empty ~f:Counter.touch

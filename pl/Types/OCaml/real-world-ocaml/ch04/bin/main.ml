(******************************************************************************
Entry point.
******************************************************************************)
open Base
open Stdio


let () = Ch04.Freq.build_counts ()
  |> Ch04.Counter.to_list
  |> List.sort ~compare:(fun (_,x) (_,y) -> Int.descending x y)
  |> (fun l -> List.take l 10)
  |> List.iter ~f:(fun (line, count) -> printf "%3d: %s\n" count line)

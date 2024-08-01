open Base
open Stdio

(******************************************************************************
  Records
  ******************************************************************************)
type point2d = { x : float; y : float }

let%test_unit "point2d" =
  printf "Tests in %s" Stdlib.__FILE__;
  let p = { x = 3.; y = -4. } in
  [%test_eq: float] p.x 3.;
  [%test_eq: float] p.y (-4.)

(* field punning *)
let magnitude { x; y } = Float.sqrt ((x **. 2.) +. (y **. 2.))
let distance v1 v2 = magnitude { x = v1.x -. v2.x; y = v1.y -. v2.y }

type circle_desc = { center : point2d; radius : float }
type rect_desc = { lower_left : point2d; width : float; height : float }
type segment_desc = { endpoint1 : point2d; endpoint2 : point2d }

(******************************************************************************
  Variant
  ******************************************************************************)
type scene_element =
  | Circle of circle_desc
  | Rect of rect_desc
  | Segment of segment_desc

let is_inside_scene_element point scene_element =
  let open Float.O in
  match scene_element with
  | Circle { center; radius } -> distance center point < radius
  | Rect { lower_left; width; height } ->
      point.x > lower_left.x
      && point.x < lower_left.x + width
      && point.y > lower_left.y
      && point.y < lower_left.y + height
  | Segment _ -> false

let is_inside_scene point scene =
  List.exists scene ~f:(fun el -> is_inside_scene_element point el)

let%test_unit "is_inside_scene" =
  [%test_eq: bool]
    (is_inside_scene { x = 3.; y = 7. }
       [ Circle { center = { x = 4.; y = 4. }; radius = 0.5 } ])
    false;
  [%test_eq: bool]
    (is_inside_scene { x = 3.; y = 7. }
       [ Circle { center = { x = 4.; y = 4. }; radius = 5.0 } ])
    true

(* Textstat module interface *)
type stats (* hidden type *)

val lines : stats -> int
val characters : stats -> int
val words : stats -> int
val sentences : stats -> int

val stats_from_channel : in_channel -> stats
val stats_from_file : string -> stats

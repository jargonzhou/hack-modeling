open Base

(* include the interface of the option module in Base *)
include module type of Option

val apply : ('a -> 'b) t -> 'a -> 'b t

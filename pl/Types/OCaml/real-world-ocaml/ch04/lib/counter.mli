open Base

type t
(** A collection of string frequency counts.  *)

val empty : t
(** The empyt set of frequency counts.  *)

(* val touch : (string * int) list -> string -> (string * int) list *)
val touch : t -> string -> t
(** Bump the frequency count for the given string. *)

val to_list : t -> (string * int) list
(** Convert to an association list. *)

(** Represents the median computed from a set of strings. In the case
    where there is an even number of choices, the one before and after
    the median is returned. *)
type median = Median of string | Before_and_after of string * string

val median : t -> median 

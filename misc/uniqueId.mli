(*
  Cours "Semantics and applications to verification"

  Marc Chevalier 2018
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

type t

val get : unit -> t

val compare : t -> t -> int

val print : Format.formatter -> t -> unit

val to_string : t -> string

(*
  Cours "Semantics and applications to verification"

  Marc Chevalier 2018
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)
module type Empty = sig end
module type S = sig
  type t
  val get : unit -> t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end


module Make (E: Empty) : S = struct
  type t = int

  let get =
    let n = ref 0 in
    fun () ->
      assert (!n <> -1);
      let x = !n in
      incr n;
      x

  let compare = Int.compare

  let print fmt uid = Format.fprintf fmt "%d" uid
end

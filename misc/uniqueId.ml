(*
  Cours "Semantics and applications to verification"

  Marc Chevalier 2018
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

type t = int

let get =
  let n = ref 0 in
  fun () ->
    assert (!n <> -1);
    let x = !n in
    incr n;
    x

let compare = Int.compare
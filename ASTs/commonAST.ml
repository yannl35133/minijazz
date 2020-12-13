(* Localize an element *)

type 'a localized =
  {
    desc: 'a;
    loc: Location.location
  }

let (!!) = fun obj -> obj.desc
let (!@) = fun obj -> obj.loc

let localize loc x = {
    desc = x;
    loc = Loc loc
  }

let relocalize loc x = {
    desc = x;
    loc
  }

let relocalize_fun f obj = relocalize !@obj (f !!obj)

let no_localize x = {
    desc = x;
    loc = Location.no_location
  }

type name = string localized
type constructor = Ident.t
type ident = Ident.t

module Env = Map.Make (struct type t = ident let compare = compare end)
module IntEnv = Map.Make (Int)
module IdentSet = Set.Make (struct type t = ident let compare = compare end)

type inline_status = Inline | NotInline

type mem_kind_desc = MRom | MRam
and mem_kind = mem_kind_desc localized

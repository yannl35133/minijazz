type constructor_desc = string
type ident_desc = string
module Env = Map.Make (struct type t = ident_desc let compare = compare end)
module IntEnv = Map.Make (Int)
module IdentSet = Set.Make (struct type t = ident_desc let compare = compare end)


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
let relocalize_fun f obj =
  relocalize !@obj (f !!obj)
let no_localize x = {
  desc = x;
  loc = Location.no_location
}

type constructor = constructor_desc localized
type ident = ident_desc localized

type inline_status = Inline | NotInline

type mem_kind_desc = MRom | MRam
and mem_kind = mem_kind_desc localized

type 'e state_expr =
  | Estate0 of ident
  | Estaten of ident * 'e list

type state_desc =
  | Estate0pat of ident
  | Estatenpat of ident * ident list

type state = state_desc localized

let state_name st = match st.desc with
  | Estate0pat id -> id
  | Estatenpat (id, _) -> id

type ('e, 'b) match_hdl = {
    m_constr: constructor;
    m_body: 'b
  }

type ('e, 'b) escape = {
    e_cond: 'e;
    e_reset: bool;
    e_body: 'b;
    e_nx_state: 'e state_expr
  }

type ('e, 'b) automaton_hdl = {
    s_state: state;
    s_vars: ident list;
    s_body: 'b;
    s_until: ('e, 'b) escape list;
    s_unless: ('e, 'b) escape list
  }

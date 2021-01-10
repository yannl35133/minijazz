type ident_desc = string
type constructor_desc = string


(* module IntEnv = Map.Make (Int) *)
(* module IdentSet = Set.Make (struct type t = ident_desc let compare = compare end) *)
module UIDIdent = UniqueId.Make ()
module UIDConstructor = UniqueId.Make ()
module UIDUnknownStatic = UniqueId.Make ()

module FunEnv = Map.Make (String)
module IdentSet = Set.Make (UIDIdent)
module Env = Map.Make (UIDIdent)
module ConstructSet = Set.Make (UIDConstructor)
module ConstructEnv = Map.Make (UIDConstructor)

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

(* Localize and identify an element *)

type ('a, 'uid) identified =
  {
    id_desc: 'a;
    id_loc: Location.location;
    id_uid: 'uid
  }

let (!*!) = fun obj -> obj.id_desc
let (!*@) = fun obj -> obj.id_loc
let (!**) = fun (obj: ('a, 'uid) identified) -> obj.id_uid

let identify loc x uid = {
  id_desc = x;
  id_loc = loc;
  id_uid = uid
}
let re_identify {desc; loc} uid = {
  id_desc = desc;
  id_loc = loc;
  id_uid = uid
}

(* These types only apply after scoping, but are defined here nonetheless *)
type ident = (ident_desc, UIDIdent.t) identified
type parameter = (ident_desc, int) identified
type constructor = (constructor_desc, UIDConstructor.t) identified

type enum = {
  enum_name: ident;
  enum_constructors_names: constructor list;
  enum_constructors: ConstructSet.t;
  enum_loc: Location.location (* ? *)
}

(* Static expressions *)

type 'static_exp_desc static_exp_option =
  | SExp of 'static_exp_desc
  | SUnknown of UIDUnknownStatic.t

type 'sttype static_typed_ident = {
  sti_name: parameter;
  sti_type: 'sttype localized;
  sti_loc:  Location.location;
}

(* Netlist / state types *)

type transition =
  | Continue
  | Reset

type state_type = enum

type state_transition_type = enum

type 'netlist_type tritype =
  | BNetlist of 'netlist_type
  | BState of state_type
  | BStateTransition of state_transition_type

type 'size netlist_type =
  | TNDim of 'size list
  | TProd of 'size netlist_type list

type 'size global_type = 'size netlist_type tritype


type 'a state_typed = {
  s_desc: 'a;
  s_loc:  Location.location;
  s_type: state_type
}

let state_type desc loc ty =
  { s_desc = desc; s_loc = loc; s_type = ty }

type 'a state_transition_typed = {
  st_desc: 'a;
  st_loc:  Location.location;
  st_type: state_transition_type
}

let state_transition_type desc loc ty =
  { st_desc = desc; st_loc = loc; st_type = ty }

type ('a, 'netlist_type) trityped = {
  b_desc: 'a;
  b_loc:  Location.location;
  b_type: 'netlist_type tritype
}

type ('a, 'size) global_typed = ('a, 'size netlist_type) trityped

let (!?!) = fun obj -> obj.b_desc
let (!?@) = fun obj -> obj.b_loc
let (!??) = fun obj -> obj.b_type

let tritype desc loc ty =
  { b_desc = desc; b_loc = loc; b_type = ty }

(* Netlist expressions *)

type value =
  | VNDim of value list
  | VBit of bool

type funname = ident_desc localized

type 'size slice_param =
  | SliceAll
  | SliceOne of  'size
  | SliceFrom of 'size
  | SliceTo of   'size
  | Slice of    ('size * 'size)


type 'size typed_ident = {
  ti_name: ident;
  ti_type: 'size global_type localized;
  ti_loc:  Location.location
}

type state = constructor

type 'decl match_handler = {
  m_state: state;
  m_hloc: Location.location;
  m_body: 'decl list
}

type 'decl matcher = {
  m_state_type: enum;
  m_loc: Location.location;
  m_handlers: 'decl match_handler ConstructEnv.t
}


type ('state_transition_exp, 'decl) automaton_handler = {
  a_state: state;
  a_hloc: Location.location;
  a_body: 'decl list;
  a_weak_transition: 'state_transition_exp;
  a_strong_transition: 'state_transition_exp;
}

type ('state_transition_exp, 'decl) automaton = {
  a_state_type: enum;
  a_loc: Location.location;
  a_fst_state: state;
  a_handlers: ('state_transition_exp, 'decl) automaton_handler ConstructEnv.t
}

type inline_status = Inline | NotInline

type mem_kind_desc = MRom | MRam
and mem_kind = mem_kind_desc localized

type 'static_exp const = {
  const_name: ident;
  const_decl: 'static_exp;
  const_loc:  Location.location;
}

type ('static_type, 'size, 'decl, 'var_info) node = {
  node_name:    funname;
  node_loc:     Location.location;
  node_params:  'static_type static_typed_ident list;
  node_inline:  inline_status;
  node_inputs:  'size typed_ident list;
  node_outputs: 'size typed_ident list;
  node_body:    'decl list;
  node_variables: 'var_info Env.t
  (* node_probes:  ident list; *)
}

type ('static_type, 'static_exp, 'size, 'decl, 'var_info) program = {
  p_enums:   enum ConstructEnv.t;
  p_consts: 'static_exp const Env.t;
  p_consts_order: UIDIdent.t list;
  p_nodes:  ('static_type, 'size, 'decl, 'var_info) node FunEnv.t;
}

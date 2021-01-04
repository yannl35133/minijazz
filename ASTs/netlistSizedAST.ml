open CommonAST
open StaticTypedPartialAST

(* Netlist expressions *)

type size =
  | Size of static_int_exp_desc


type netlist_sized =
  | TProd of netlist_sized list
  | TDim of size list

type 'a sized =
  {
    s_desc: 'a;
    s_loc: Location.location;
    s_size: netlist_sized
  }

let (!$!) = fun obj -> obj.s_desc
let (!$@) = fun obj -> obj.s_loc
let (!$$) = fun obj -> obj.s_size

let size desc loc size =
  { s_desc = desc; s_loc = loc; s_size = size }

type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc sized

type exp_desc =
  | EConst  of ParserAST.value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_bitype_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (static_int_exp * static_int_exp * string option) * exp list
(* ro * (address size * word size * input file) * args *)
  | EMatch  of exp * (exp, decl) match_hdl list

and exp = exp_desc sized

and decl_desc =
  | Dempty
  | Deq        of lvalue * exp (* p = e *)
  | Dblock     of decl list (* eq1; ... ; eqn *)
  | Dreset     of decl * exp (* reset eq every e *)
  | Dautomaton of (exp, decl) automaton_hdl list
  | Dif        of static_bool_exp * case * case
and decl = decl_desc localized

and case = {
    block:     decl;
    dim_env:   netlist_sized Env.t;
  }

type typed_ident_desc = {
  name: ident;
  size: netlist_sized localized
}
and typed_ident = typed_ident_desc localized


type fun_env = static_type list Env.t

type node = {
  node_name_loc:  Location.location;
  node_loc:       Location.location;
  node_params:    static_typed_ident list;
  node_inline:    inline_status;
  node_inputs:    typed_ident list;
  node_outputs:   typed_ident list;
  node_body:      decl;
  node_probes:    ident list;
}

type program = {
  p_consts: StaticTypedPartialAST.const Env.t;
  p_consts_order: ident_desc list;
  p_nodes:  node  Env.t;
}

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

type exp_desc =
  | EConst  of ParserAST.value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_bitype_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (static_int_exp * static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc sized

type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc sized

type equation_desc = {
  eq_left:  lvalue;
  eq_right: exp
}
and equation = equation_desc localized


type typed_ident_desc = {
  name: ident;
  size: netlist_sized localized
}
and typed_ident = typed_ident_desc localized

type case = {
  equations: equation list;
  dim_env:   netlist_sized Env.t;
}

type block_desc =
  | BEqs of case
  | BIf  of static_bool_exp * block * block

and block = block_desc localized

type fun_env = static_type list Env.t

type node = {
  node_name_loc:  Location.location;
  node_loc:       Location.location;
  node_params:    static_typed_ident list;
  node_inline:    inline_status;
  node_inputs:    typed_ident list;
  node_outputs:   typed_ident list;
  node_body:      block;
  node_probes:    ident list;
}

type program = {
  p_consts: StaticTypedPartialAST.const Env.t;
  p_consts_order: ident_desc list;
  p_nodes:  node  Env.t;
}

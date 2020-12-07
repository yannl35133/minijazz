open CommonAST
open StaticTypedPartialAST

(* Netlist expressions *)

type netlist_dimension =
  | NProd of netlist_dimension list
  | NDim of int

type 'a dimensioned =
  {
    dim_desc: 'a;
    dim_loc: Location.location;
    dim_nb: netlist_dimension
  }

let (!%!) = fun obj -> obj.dim_desc
let (!%%) = fun obj -> obj.dim_nb
let (!%@) = fun obj -> obj.dim_loc

let dimension desc loc dim =
  { dim_desc = desc; dim_loc = loc; dim_nb = dim }

type exp_desc =
  | EConst  of ParserAST.value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc dimensioned

type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc dimensioned

type equation_desc = {
  eq_left:  lvalue;
  eq_right: exp
}
and equation = equation_desc localized


type typed_ident_desc = {
  name:  ident;
  typed: StaticTypedAST.netlist_type localized;
  dim: netlist_dimension
}
and typed_ident = typed_ident_desc localized

type case = {
  equations: equation list;
  dim_env: netlist_dimension Env.t
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

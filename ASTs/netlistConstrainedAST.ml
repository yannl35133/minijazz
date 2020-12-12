open CommonAST
open StaticTypedPartialAST

(* Netlist expressions *)

type size_constraints_reason =
  | CFunArg of ident_desc * int
  | CFunRet of ident_desc
  | CRomArg
  | CRomRet
  | CRamArg of int
  | CRamRet

type presize =
  | PSVar of ident * int * UniqueId.t
  | PSParam of ident_desc * int * UniqueId.t * Location.location
  | PSConst of static_int_exp
  | PSSub of presize * presize

type size_constraint_equality =
  presize * presize


type netlist_presized_dimensioned =
  | CDProd of netlist_presized_dimensioned list
  | CDDim of presize list

type 'a presized =
  {
    ps_desc: 'a;
    ps_loc: Location.location;
    ps_size: netlist_presized_dimensioned
  }

let (!$!) = fun obj -> obj.ps_desc
let (!$@) = fun obj -> obj.ps_loc
let (!$$) = fun obj -> obj.ps_size

let presize desc loc size =
  { ps_desc = desc; ps_loc = loc; ps_size = size }

type exp_desc =
  | EConst  of ParserAST.value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc presized

type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc presized

type equation_desc = {
  eq_left:  lvalue;
  eq_right: exp
}
and equation = equation_desc localized


type typed_ident_desc = {
  name:  ident;
  presize: netlist_presized_dimensioned localized
}
and typed_ident = typed_ident_desc localized

type case = {
  equations: equation list;
  dim_env: netlist_presized_dimensioned Env.t;
  constraints: size_constraint_equality list
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

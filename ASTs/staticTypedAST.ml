open CommonAST
include StaticTypedPartialAST

(* Netlist expressions *)

type netlist_type =
  | TBitArray of optional_static_int_exp
  | TProd of netlist_type list

  type slice_param =
  | SliceAll
  | SliceFrom of optional_static_int_exp
  | SliceTo of optional_static_int_exp
  | Slice of (optional_static_int_exp * optional_static_int_exp)

type exp_desc =
  | EConst of ParserAST.value
  | EVar   of ident
  | EReg   of exp
  | ESelect of optional_static_int_exp list * exp
  | ESlice  of slice_param list * exp
  | ESupOp  of ident * exp list 
  | ECall  of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem   of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc localized

type equation_desc = {
  eq_left:  ParserAST.lvalue;
  eq_right: exp
}
and equation = equation_desc localized


type typed_ident_desc = {
  name:  ident;
  typed: netlist_type localized;
}
and typed_ident = typed_ident_desc localized


type block_desc =
  | BEqs of equation list
  | BIf  of static_bool_exp * block * block

and block = block_desc localized

type static_typed_ident_desc = {
  st_name: ident;
  st_type: static_type localized;
}
and static_typed_ident = static_typed_ident_desc localized

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

type const = {
  const_decl:  static_unknown_exp;
  const_ident: Location.location;
  const_total: Location.location;
}

type program = {
  p_consts: const Env.t;
  p_consts_order: ident_desc list;
  p_nodes:  node  Env.t;
}

open CommonAST
open StaticTypedPartialAST

(** 3rd Ast: static expressions are typed *)

(* Netlist expressions *)

type netlist_type =
  | TNDim of optional_static_int_exp list
  | TProd of netlist_type list

type slice_param =
  | SliceAll
  | SliceOne of  optional_static_int_exp
  | SliceFrom of optional_static_int_exp
  | SliceTo of   optional_static_int_exp
  | Slice of    (optional_static_int_exp * optional_static_int_exp)

type exp_desc =
  | EConst  of ParserAST.value
  | EConstr of exp ParserAST.state_expr
  | EVar    of ident
  | EReg    of exp
  | ESlice  of slice_param list * exp
  | ESupOp  of ident * exp list
  | ECall   of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
(* ro * (address size * word size * input file) * args *)
  | ELet    of eq * exp
  | EMerge  of exp * (exp, eq) ParserAST.match_hdl list

and exp = exp_desc localized

and eq_desc =
  | EQempty
  | EQeq        of ParserAST.lvalue * exp (* p = e *)
  | EQand       of eq list (* eq1; ... ; eqn *)
  | EQlet       of eq * eq (* let eq in eq *)
  | EQreset     of eq * exp (* reset eq every e *)
  | EQautomaton of (exp, eq) ParserAST.automaton_hdl list
  | EQmatch     of exp * (exp, eq) ParserAST.match_hdl list

and eq = eq_desc localized


type typed_ident_desc = {
  name:  ident;
  typed: netlist_type localized;
}
and typed_ident = typed_ident_desc localized


type block_desc =
  | BEqs of eq list
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

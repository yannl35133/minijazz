open CommonAST
open StaticTypedPartialAST

(** 4th AST: expressions are assigned dimensions / state status *)

type size = optional_static_int_exp

(* Netlist expressions *)

type netlist_dimension =
  | NProd of netlist_dimension list
  | NDim of int

type global_type = netlist_dimension CommonAST.tritype
type global_type' = size CommonAST.global_type

type 'a global_typed = ('a, netlist_dimension) CommonAST.trityped

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
  | EConst  of value
  | EVar    of ident
  | EReg    of exp
  | ECall   of funname * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc dimensioned

type tritype_exp = exp StaticTypedPartialAST.tritype_exp

type lvalue = {
  lval: netlist_dimension lvalue0;
  lval_type: global_type' option localized
}

type typed_ident = size CommonAST.typed_ident

type automaton = ((exp * exp state_transition_exp) list, decl) CommonAST.automaton

and decl_desc =
  | Deq        of lvalue * tritype_exp (* p = e *)
  | Dlocaleq   of lvalue * tritype_exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of automaton
  | Dmatch     of exp state_exp * decl matcher
  | Dif        of static_bool_exp * decl list * decl list

and decl = decl_desc localized


type fun_env = (netlist_dimension list * netlist_dimension) FunEnv.t

type node = (static_type, size, decl, ident global_typed) CommonAST.node
type const = static_bitype_exp CommonAST.const
type program = (static_type, static_bitype_exp, size, decl, ident global_typed) CommonAST.program

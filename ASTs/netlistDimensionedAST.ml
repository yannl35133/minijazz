open CommonAST
open StaticTypedPartialAST

(** 4th AST: expressions are assigned dimensions / state status *)

type size = optional_static_int_exp

(* Netlist expressions *)

type netlist_dimension =
  | NProd of netlist_dimension list
  | NDim of int

type global_type = netlist_dimension CommonAST.bitype

type 'a dimensioned = ('a, netlist_dimension) bityped

let dimension: 'a -> 'b -> 'c -> 'a dimensioned = bitype

type exp_desc =
  | EConst  of value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc dimensioned

type bitype_exp = exp StaticTypedPartialAST.bitype_exp

type lvalue = netlist_dimension StaticTypedPartialAST.lvalue

type typed_ident = size CommonAST.typed_ident


type decl_desc =
  | Deq        of lvalue * bitype_exp (* p = e *)
  | Dlocaleq   of lvalue * bitype_exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of ((exp * state_transition_exp) list, decl) automaton
  | Dmatch     of state_exp * decl matcher
  | Dif        of static_bool_exp * decl list * decl list

and decl = decl_desc localized


type fun_env = static_type list Env.t

type node = (static_type, size, decl) CommonAST.node
type const = static_bitype_exp CommonAST.const
type program = (static_type, static_bitype_exp, size, decl) CommonAST.program

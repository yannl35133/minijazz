open CommonAST
open StaticTypedPartialAST

(** Final analysis AST : netlist expression dimensions are assigned values (expressions of parameters) *)

(* Netlist expressions *)

type size =
  | Size of static_int_exp_desc


type netlist_size = size CommonAST.netlist_type

type global_size = size CommonAST.global_type

type 'a sized = ('a, netlist_size) bityped

let size: 'a -> 'b -> 'c -> 'a sized = bitype

type exp_desc =
  | EConst  of value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_bitype_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (static_int_exp * static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc sized

type bitype_exp = exp StaticTypedPartialAST.bitype_exp

type lvalue = netlist_size StaticTypedPartialAST.lvalue

type typed_ident = size CommonAST.typed_ident

type decl_desc =
  | Deq        of lvalue * bitype_exp (* p = e *)
  | Dlocaleq   of lvalue * bitype_exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of ((exp * state_transition_exp) list, decl) automaton
  | Dmatch     of state_exp * decl matcher
  | Dif        of static_bool_exp * decl list * decl list (*netlist_size Env.t ??*)

and decl = decl_desc localized


type fun_env = static_type list Env.t

type node = (static_type, size, decl) CommonAST.node
type const = static_bitype_exp CommonAST.const
type program = (static_type, static_bitype_exp, size, decl) CommonAST.program

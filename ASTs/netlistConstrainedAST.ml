open CommonAST
open StaticTypedPartialAST

(** 5th AST: netlist expression dimensions are assigned value / unknown uid *)

(* Netlist expressions *)

type presize =
  | PSVar of ident * int * UIDUnknownStatic.t
  | PSConst of static_int_exp
  | PSOtherContext of ident_desc * Location.location * static_unknown_exp list * presize

type size_constraint_equality =
  presize * presize


type netlist_presize = presize CommonAST.netlist_type

type global_presize = presize CommonAST.global_type

type 'a presized = ('a, netlist_presize) bityped

let presize: 'a -> 'b -> 'c -> 'a presized = bitype

type exp_desc =
  | EConst  of value
  | EVar    of ident
  | EReg    of exp
  | ECall   of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc presized

type bitype_exp = exp StaticTypedPartialAST.bitype_exp

type lvalue = netlist_presize StaticTypedPartialAST.lvalue

type typed_ident = presize CommonAST.typed_ident


type decl_desc =
  | Deq        of lvalue * bitype_exp (* p = e *)
  | Dlocaleq   of lvalue * bitype_exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of ((exp * state_transition_exp) list, decl) automaton
  | Dmatch     of state_exp * decl matcher
  | Dif        of static_bool_exp * decl list * decl list (*netlist_presize Env.t ??*)

and decl = decl_desc localized


type fun_env = static_type list Env.t

type node = (static_type, presize, decl) CommonAST.node
type const = static_bitype_exp CommonAST.const
type preprogram = (static_type, static_bitype_exp, presize, decl) CommonAST.program

type program = preprogram * size_constraint_equality list

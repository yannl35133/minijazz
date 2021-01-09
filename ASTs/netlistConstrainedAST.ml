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

type 'a presized = {
  ps_desc: 'a;
  ps_loc: Location.location;
  ps_size: netlist_presize
}

let (!&!) = fun obj -> obj.ps_desc
let (!&@) = fun obj -> obj.ps_loc
let (!&&) = fun obj -> obj.ps_size

let presize desc loc size =
  { ps_desc = desc; ps_loc = loc; ps_size = size }

type exp_desc =
  | EConst  of value
  | EVar    of ident
  | EReg    of exp
  | ECall   of funname * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc presized

type tritype_exp = exp StaticTypedPartialAST.tritype_exp

type lvalue = netlist_presize StaticTypedPartialAST.lvalue

type typed_ident = presize CommonAST.typed_ident


type decl_desc =
  | Deq        of lvalue * tritype_exp (* p = e *)
  | Dlocaleq   of lvalue * tritype_exp (* local p = e *)
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

open CommonAST
open StaticTypedPartialAST

(** 3rd AST: static expressions are typed *)

type size = optional_static_int_exp

(* Netlist expressions *)
type netlist_type = size CommonAST.netlist_type
type global_type = size CommonAST.global_type

type slice_param = size CommonAST.slice_param

type exp_desc =
  | EConst  of value
  | EConstr of constructor
  | EVar    of ident
  | EContinue of exp
  | ERestart of exp
  | EReg    of exp
  | ESlice  of slice_param list * exp
  | ESupOp  of funname * exp list
  | ECall   of funname * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc localized

type lvalue = {
  lval: CommonAST.lvalue0;
  lval_type: global_type option localized
}

type typed_ident = size CommonAST.typed_ident

type automaton = ((exp * exp) list, decl) CommonAST.automaton

and decl_desc =
  | Deq        of lvalue * exp (* p = e *)
  | Dlocaleq   of lvalue * exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of automaton
  | Dmatch     of exp * decl matcher
  | Dif        of static_bool_exp * decl list * decl list

and decl = decl_desc localized


type fun_env = static_type list FunEnv.t

type node = (static_type, size, decl, ident) CommonAST.node
type const = static_bitype_exp CommonAST.const
type program = (static_type, static_bitype_exp, size, decl, ident) CommonAST.program

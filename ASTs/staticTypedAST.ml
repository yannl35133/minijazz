open CommonAST
open StaticTypedPartialAST

(** 3rd AST: static expressions are typed *)

type size = optional_static_int_exp

(* Netlist expressions *)
type netlist_type = size CommonAST.netlist_type

type slice_param = size CommonAST.slice_param

type exp_desc =
  | EConst  of value
  | EConstr of constructor
  | EVar    of ident
  | EReg    of exp
  | ESlice  of slice_param list * exp
  | ESupOp  of ident * exp list
  | ECall   of ident * static_unknown_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_int_exp * optional_static_int_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc localized

type typed_ident = size CommonAST.typed_ident

type decl_desc =
  | Deq        of ParserAST.lvalue * exp (* p = e *)
  | Dlocaleq   of ParserAST.lvalue * exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of ((exp * exp) list, decl) automaton
  | Dmatch     of exp * decl matcher
  | Dif        of static_bool_exp * decl list * decl list

and decl = decl_desc localized


type fun_env = static_type list Env.t

type node = (static_type, size, decl) CommonAST.node
type const = static_bitype_exp CommonAST.const
type program = (static_type, static_bitype_exp, size, decl) CommonAST.program

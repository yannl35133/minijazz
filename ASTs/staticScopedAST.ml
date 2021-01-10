open CommonAST

(** Second Ast, resolve name domain *)

type sunop = ParserAST.sunop
type sop =   ParserAST.sop

type static_exp_desc = (* Removed SPar *)
  | SInt   of int
  | SBool  of bool
  | SConst of ident
  | SParam of parameter
  | SUnOp  of      sunop * static_exp
  | SBinOp of        sop * static_exp * static_exp
  | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

and static_exp = static_exp_desc localized

type optional_static_exp = static_exp_desc static_exp_option localized

type static_type = ident_desc (* ideally, "bool" or "int "*)
type static_typed_ident = static_type CommonAST.static_typed_ident


(* Netlist expressions *)
type size = optional_static_exp

type netlist_type = size CommonAST.netlist_type

type slice_param = size CommonAST.slice_param

type exp_desc = (* Removed EPar *)
  | EConst  of value
  | EConstr of constructor
  | EVar    of ident
  | EContinue of exp
  | ERestart of exp
  | EReg    of exp
  | ESlice  of slice_param list * exp
  | ESupOp  of funname * exp list
  | ECall   of funname * optional_static_exp list * exp list
      (* function * params * args *)
  | EMem    of mem_kind * (optional_static_exp * optional_static_exp * string option) * exp list
      (* ro * (address size * word size * input file) * args *)

and exp = exp_desc localized

type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc localized

type typed_ident = size CommonAST.typed_ident

type decl_desc =
  | Deq        of lvalue * exp (* p = e *)
  | Dlocaleq   of lvalue * exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of ((exp * exp) list, decl) automaton
  | Dmatch     of exp * decl matcher
  | Dif        of static_exp * decl list * decl list

and decl = decl_desc localized


type node = (static_type, size, decl) CommonAST.node
type const = static_exp CommonAST.const
type program = (static_type, static_exp, size, decl) CommonAST.program

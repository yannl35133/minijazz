open CommonAST

type static_type =
  | TInt
  | TBool

let static_type_to_string = function
  | TInt -> "int"
  | TBool -> "bool"

let static_type_of_string id =
  match !!id with
    | "int" -> TInt
    | "bool" -> TBool
    | _ -> raise @@ Errors.NotAType (!!id, !@id)

type int_op = SAdd | SMinus | SMult | SDiv | SPower
type int_bool_op = SEq | SNeq | SLt | SLeq | SGt | SGeq
type bool_op = SOr | SAnd

type int_unop = SNeg
type bool_unop = SNot

type static_int_exp_desc =
  | SInt    of int
  | SIParam of parameter
  | SIConst of ident
  | SIUnOp  of        int_unop * static_int_exp
  | SIBinOp of          int_op * static_int_exp * static_int_exp
  | SIIf    of static_bool_exp * static_int_exp * static_int_exp  (* se1 ? se2 : se3 *)

and static_bool_exp_desc =
  | SBool   of bool
  | SBParam of parameter
  | SBConst of ident
  | SBUnOp  of       bool_unop * static_bool_exp
  | SBBinOp of         bool_op * static_bool_exp * static_bool_exp
  | SBBinIntOp of  int_bool_op * static_int_exp  * static_int_exp
  | SBIf    of static_bool_exp * static_bool_exp * static_bool_exp  (* se1 ? se2 : se3 *)

and static_int_exp  = static_int_exp_desc  localized
and static_bool_exp = static_bool_exp_desc localized


type static_unknown_exp_desc =
  | SOIntExp  of static_int_exp_desc  static_exp_option
  | SOBoolExp of static_bool_exp_desc static_exp_option
and static_unknown_exp = static_unknown_exp_desc localized

type static_bitype_exp_desc =
  | SIntExp  of static_int_exp_desc
  | SBoolExp of static_bool_exp_desc
and static_bitype_exp = static_bitype_exp_desc localized

type optional_static_int_exp_desc = static_int_exp_desc static_exp_option
and optional_static_int_exp = optional_static_int_exp_desc localized

type static_typed_ident = static_type CommonAST.static_typed_ident


(* State expressions *)

type 'exp state_exp_desc =
  | EConstr of constructor
  | ESMux of ('exp * 'exp state_exp * 'exp state_exp)
  (* | ECall   of funname * static_unknown_exp list * exp list *)
    (* function * params * args *)

and 'exp state_exp = 'exp state_exp_desc state_typed

and 'exp state_transition_exp_desc =
  | EContinue of 'exp state_exp
  | ERestart  of 'exp state_exp
  (* | ECall   of funname * static_unknown_exp list * exp list *)
    (* function * params * args *)

and 'exp state_transition_exp = 'exp state_transition_exp_desc state_transition_typed

type 'exp tritype_exp =
  | Exp of 'exp
  | StateExp of 'exp state_exp
  | StateTransitionExp of 'exp state_transition_exp

type 'netlist_type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of 'netlist_type lvalue list

and 'netlist_type lvalue = ('netlist_type lvalue_desc, 'netlist_type) trityped

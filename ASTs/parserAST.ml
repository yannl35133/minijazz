(***********************************************************************)
(*                                                                     *)
(*                             MiniJazz                                *)
(*                                                                     *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(*                                                                     *)
(* Copyright 2013 ENS                                                  *)
(*                                                                     *)
(* This file is part of the MiniJazz compiler.                         *)
(*                                                                     *)
(* MiniJazz is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* MiniJazz is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with MiniJazz.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)


(** Parsing Ast is produced by lexer/parser *)

open CommonAST

(* Overwrite definitions for post-scoped ASTs *)
type ident = ident_desc localized
type constructor = constructor_desc localized

(* list of defined enum types
   can't be produced by input program *)
type enum = {
  enum_name: ident;
  enum_constructors: constructor list;
  enum_loc: Location.location (* ? *)
}


(* Static expressions *)

type sop =
  | SAdd | SMinus | SMult | SDiv | SPower (* int -> int *)
  | SEq | SNeq | SLt | SLeq | SGt | SGeq  (* int -> bool *)
  | SOr | SAnd                            (* bool -> bool *)


type sunop = SNeg | SNot

type static_exp_desc =
  | SInt   of int
  | SBool  of bool
  | SIdent of ident
  | SPar   of static_exp                            (* Created purely to have good locations *)
  | SUnOp  of      sunop * static_exp
  | SBinOp of        sop * static_exp * static_exp
  | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

and static_exp = static_exp_desc localized

type optional_static_exp = static_exp_desc static_exp_option localized

type static_typed_ident = {
  sti_name: ident;
  sti_type: ident; (* ideally, ident is "int" or "bool" *)
  sti_loc:  Location.location;
}

(* Netlist expressions *)

type netlist_type =
  | TNDim of optional_static_exp list
  | TProd of netlist_type list

type global_type =
  | BNetlist of netlist_type
  | BState of ident (* ideally, ident is one of the defined enums *)
  | BStateTransition of ident

type slice_param = optional_static_exp CommonAST.slice_param

type exp_desc =
  | EConst  of value
  | EConstr of constructor
  | EVar    of ident
  | EContinue of exp
  | ERestart of exp
  | EPar    of exp     (* Created purely to have good locations *)
  | EReg    of exp
  | ESupOp  of ident * exp list
  | ESlice  of slice_param list * exp
  | ECall   of ident * optional_static_exp list * exp list
  (* function * params * args *)
  | EMem    of mem_kind * (optional_static_exp * optional_static_exp * string option) * exp list
and exp = exp_desc localized


type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue0 list

and lvalue0 = lvalue_desc localized

type lvalue = {
  lval: lvalue0;
  lval_type: global_type option localized
}

type typed_ident = {
  ti_name: ident;
  ti_type: global_type localized;
  ti_loc:  Location.location
}

(* may change if states can take parameters *)
(* type 'e state_expr = ident *)
type state = constructor

type match_handler = {
  m_state: state;
  m_hloc: Location.location;
  m_body: decl list;
}

and matcher = {
  m_handlers: match_handler list;
  m_loc: Location.location;
}


and automaton_handler = {
  a_state: state;
  a_hloc: Location.location;
  a_body: decl list;
  a_weak_transition: (exp * exp) list;
  a_strong_transition: (exp * exp) list;
}

and automaton = {
  a_handlers: automaton_handler list;
  a_loc: Location.location;
}

and decl_desc =
  | Deq        of lvalue * exp (* p = e *)
  | Dlocaleq   of lvalue * exp (* local p = e *)
  | Dreset     of exp * decl list (* reset eq every e *)
  | Dautomaton of automaton
  | Dmatch     of (exp * matcher)
  | Dif        of static_exp * decl list * decl list

and decl = decl_desc localized



type node = {
  node_name:    ident;
  node_loc:     Location.location;
  node_inline:  inline_status;
  node_inputs : typed_ident list;
  node_outputs: typed_ident list;
  node_params : static_typed_ident list;
  node_body:    decl list localized;
  (* n_constraints : static_exp list; *)
  node_probes : ident list;
}

type const = {
  const_left: ident;
  const_right: static_exp;
  const_loc: Location.location
}

type program = {
  p_enums:  enum list;
  p_consts: const list;
  p_nodes:  node list;
}

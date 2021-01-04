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

open CommonAST

(** Parsing Ast is produced by lexer/parser *)

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

type optional_static_exp_desc =
  | SExp of static_exp_desc
  | SUnknown of UniqueId.t
and optional_static_exp = optional_static_exp_desc localized

type static_typed_ident_desc = {
  st_name:      ident;
  st_type_name: ident; (* ideally, "int" or "bool" *)
}
and static_typed_ident = static_typed_ident_desc localized


(* Netlist expressions *)

type netlist_type =
  | TNDim of optional_static_exp list
  | TProd of netlist_type list



type value =
  | VNDim of value list
  | VBit of bool

type slice_param =
  | SliceAll
  | SliceOne of  optional_static_exp
  | SliceFrom of optional_static_exp
  | SliceTo of   optional_static_exp
  | Slice of    (optional_static_exp * optional_static_exp)

type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc localized

type exp_desc =
  | EConst  of value
  | EVar    of ident
  | EPar    of exp     (* Created purely to have good locations *)
  | EReg    of exp
  | ESupOp  of ident * exp list
  | ESlice  of slice_param list * exp
  | ECall   of ident * optional_static_exp list * exp list
  (* function * params * args *)
  | EMem    of mem_kind * (optional_static_exp * optional_static_exp * string option) * exp list
  | EMatch  of exp * (exp, decl) match_hdl list

and exp = exp_desc localized

and decl_desc =
  | Dempty
  | Deq        of lvalue * exp (* p = e *)
  | Dand       of decl list (* eq1; ... ; eqn *)
  | Dreset     of decl * exp (* reset eq every e *)
  | Dautomaton of (exp, decl) automaton_hdl list
  | Dif        of static_exp * decl * decl
and decl = decl_desc localized


type typed_ident_desc = {
  name : ident;
  typed : netlist_type localized;
}
and typed_ident = typed_ident_desc localized


type node_desc = {
  node_name:    ident;
  node_inline:  inline_status;
  node_inputs : typed_ident list;
  node_outputs: typed_ident list;
  node_params : static_typed_ident list;
  node_body:    decl;
  (* n_constraints : static_exp list; *)
  node_probes : ident list;
}
and node = node_desc localized

type const_desc = {
  const_left: ident;
  const_right: static_exp;
}
and const = const_desc localized

type program = {
  p_consts: const list;
  p_nodes : node list;
}

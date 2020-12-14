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

type static_type = TInt | TBool

let static_type_to_string = function
  | TInt -> "int"
  | TBool -> "bool"

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

type optional_static_exp_desc = static_exp_desc option
and optional_static_exp = optional_static_exp_desc localized

type static_typed_ident = {
  st_name:      ident;
  st_type_name: name; (* ideally, "int" or "bool" *)
  st_loc: Location.location;
}

(* Netlist expressions *)

type ty =
  | TUnit | TBit | TBitArray of static_exp | TProd of ty list
  | TVar of link ref
and link =
  | TIndex of int
  | TLink of ty
let invalid_type = TUnit

let rec type_to_string = function
  | TUnit -> "unit"
  | TBit -> "[1]"
  | TBitArray _ -> assert false (* TODO *)
  | TProd ts -> String.concat " * " (List.map type_to_string ts)
  | TVar _ -> assert false

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

type 'e state_expr =
  | Estate0 of ident
  | Estaten of ident * 'e list

type state_desc =
  | Estate0pat of ident
  | Estatenpat of ident * ident list

type state = state_desc localized

let state_name st = match st.desc with
  | Estate0pat id -> id
  | Estatenpat (id, _) -> id

type ('e, 'b) match_hdl = {
    m_constr: constructor;
    m_body: 'b
  }

type ('e, 'b) escape = {
    e_cond: 'e;
    e_reset: bool;
    e_body: 'b;
    e_nx_state: 'e state_expr
  }

type ('e, 'b) automaton_hdl = {
    s_state: state;
    s_vars: ident list;
    s_body: 'b;
    s_until: ('e, 'b) escape list;
    s_unless: ('e, 'b) escape list
  }

type exp_desc =
  | EConst  of value
  | EConstr of exp state_expr
  | EVar    of ident
  | EPar    of exp     (* Created purely to have good locations *)
  | EReg    of exp
  | ESupOp  of name * exp list
  | ESlice  of slice_param list * exp
  | ECall   of ident * optional_static_exp list * exp list
  (* function * params * args *)
  | EMem    of mem_kind * (optional_static_exp * optional_static_exp * name option) * exp list
  | ELet    of decl * exp
  | EMerge  of exp * (exp, decl) match_hdl list
  | EMatch  of exp * (exp, decl) match_hdl list
and exp = exp_desc localized

and decl_desc =
  | Dempty
  | Deq        of lvalue * exp (* p = e *)
  | Dand       of decl list (* eq1; ... ; eqn *)
  | Dlet       of decl * decl (* let eq in eq *)
  | Dreset     of decl * exp (* reset eq every e *)
  | Dautomaton of (exp, decl) automaton_hdl list
  | Dif        of static_exp * decl * decl
and decl = decl_desc localized

type typed_ident = {
    name : ident;
    typed : netlist_type localized;
    loc: Location.location
  }

type node = {
    node_name:    ident;
    node_inline:  inline_status;
    node_inputs : typed_ident list;
    node_outputs: typed_ident list;
    node_params : static_typed_ident list;
    node_body:    decl;
    node_probes : ident list;
    node_loc :    Location.location
  }

type const = {
    const_left: ident;
    const_right: static_exp;
    const_loc: Location.location
  }

type enum = {
    enum_name: ident;
    enum_pats: constructor list;
    enum_loc: Location.location
  }

type program = {
    p_consts: const list;
    p_enums: enum list;
    p_nodes : node list;
  }

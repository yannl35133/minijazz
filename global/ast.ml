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
(* open Location
open Static *)

(* type ident = Ident.t
type name = string

module IdentEnv = Map.Make (struct type t = ident let compare = compare end)
module IdentSet = Set.Make (struct type t = ident let compare = compare end)

module NameEnv = Map.Make (struct type t = name let compare = compare end)
module NameSet = Set.Make (struct type t = name let compare = compare end) *)

type ident = string

type 'a localized =
  {
    desc: 'a;
    loc: Location.location
  }

let (!!) = fun obj -> obj.desc

(* Static expressions *)

type sop =
  | SAdd | SMinus | SMult | SDiv | SPower     (* int *)
  | SEq | SNeq | SLt | SLeq | SGt | SGeq      (* bool *)
  | SOr | SAnd

type static_exp_desc =
  | SInt   of int
  | SBool  of bool
  | SConst of ident
  | SPar   of static_exp                            (* Created purely to have good locations *)
  | SBinOp of        sop * static_exp * static_exp
  | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

and static_exp = static_exp_desc localized

type optional_static_exp_desc = static_exp_desc option
and optional_static_exp = optional_static_exp_desc localized

type static_type = TInt | TBool


type typ =
  | TUntyped
  | TBit
  | TBitArray of optional_static_exp
  | TProd of typ list
let invalid_type = TUntyped

type mem_kind = MRom | MRam

type value =
  | VBit      of bool
  | VBitArray of bool array

type exp_desc =
  | EConst of value
  | EVar   of ident
  | EPar   of exp     (* Created purely to have good locations *)
  | EReg   of exp
  | ECall  of ident * optional_static_exp list * exp list
      (* function * params * args *)
  | EMem   of mem_kind * static_exp * static_exp * string option * exp list
      (* ro * address size * word size * input file * args *)

and exp = exp_desc localized


type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc localized


type equation_desc = {
  eq_left: lvalue;
  eq_right: exp
}
and equation = equation_desc localized

type typed_ident_desc = {
  name : ident;
  typed : typ;
}
and typed_ident = typed_ident_desc localized

(* type param = {
  p_name : name;
} *)

type block_desc =
    | BEqs of equation list
    | BIf of static_exp * block * block

and block = block_desc localized

type inline_status = Inline | NotInline

type node_desc = {
  node_name:    ident;
  node_inline:  inline_status;
  node_inputs : typed_ident list;
  node_outputs: typed_ident list;
  node_params : ident list;
  node_body:    block;
  (* n_constraints : static_exp list; *)
  node_probes : ident list;
}
and node = node_desc localized

type const_desc = {
  const_left: ident;
  const_right : static_exp;
}
and const = const_desc localized

type program = {
  p_consts: const list;
  p_nodes : node list;
}

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

type optional_static_exp_desc = static_exp_desc option
and optional_static_exp = optional_static_exp_desc localized

type static_typed_ident_desc = {
  st_name:      ident;
  st_type_name: ident; (* ideally, "int" or "bool" *)
}
and static_typed_ident = static_typed_ident_desc localized


(* Netlist expressions *)

type netlist_type =
  | TBitArray of optional_static_exp
  | TProd of netlist_type list

let tbit n loc =
  TBitArray (localize loc (Some (SInt n)))

type value =
  | VBitArray of bool array

type exp_desc =
  | EConst of value
  | EVar   of ident
  | EPar   of exp     (* Created purely to have good locations *)
  | EReg   of exp
  | ESupOp of ident * exp list
  | ESlice of (optional_static_exp option * optional_static_exp option) list * exp
  | ESelect of optional_static_exp list * exp
  | ECall  of ident * optional_static_exp list * exp list
      (* function * params * args *)
  | EMem   of mem_kind * (optional_static_exp * optional_static_exp * string option) * exp list
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
  typed : netlist_type localized;
}
and typed_ident = typed_ident_desc localized


type block_desc =
    | BEqs of equation list
    | BIf  of static_exp * block * block

and block = block_desc localized


type node_desc = {
  node_name:    ident;
  node_inline:  inline_status;
  node_inputs : typed_ident list;
  node_outputs: typed_ident list;
  node_params : static_typed_ident list;
  node_body:    block;
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

(* 
module TypedAST = struct

(* Types and typed expressions *)

type static_type =
  | TInt
  | TBool

type 'a static_typed =
  {
    st_desc: 'a;
    st_type: static_type;
    st_loc: Location.location
  }

let (!$!) = fun obj -> obj.st_desc
let (!$$) = fun obj -> obj.st_type
let (!$@) = fun obj -> obj.st_loc

(* let static_type { desc; loc } t = {
  st_desc = desc;
  st_type = t;
  st_loc = loc
} *)

(* Static expressions *)

type int_op = SAdd | SMinus | SMult | SDiv | SPower
type int_bool_op = SEq | SNeq | SLt | SLeq | SGt | SGeq
type bool_op = SOr | SAnd

type sop =
  | IntOp of int_op
  | IntBoolOp of int_bool_op
  | BoolOp of bool_op

type int_unop = SNeg
type bool_unop = SNot
type sunop = IntUnop of int_unop | BoolUnop of bool_unop

type static_exp_desc =
  | SInt   of int
  | SBool  of bool
  | SIdent of ident
  | SUnOp  of      sunop * static_exp
  | SBinOp of        sop * static_exp * static_exp
  | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

and static_exp = static_exp_desc static_typed


(* Netlist expressions *)

type netlist_type =
  | TBit
  | TBitArray of static_exp
  | TProd of netlist_type list

type 'a netlist_typed =
  {
    nl_desc: 'a;
    nl_type: netlist_type;
    nl_loc: Location.location
  }

let (!&!) = fun obj -> obj.nl_desc
let (!&&) = fun obj -> obj.nl_type
let (!&@) = fun obj -> obj.nl_loc

(* let netlist_type { desc; loc } t = {
  nl_desc = desc;
  nl_type = t;
  nl_loc = loc
} *)

type mem_kind_desc = MRom | MRam
and mem_kind = mem_kind_desc localized

type value =
  | VBit      of bool
  | VBitArray of bool array

type netlist_exp_desc =
  | EConst of value
  | EVar   of ident
  | EReg   of netlist_exp
  | ECall  of ident_desc * static_exp list * netlist_exp list
      (* function * params * args *)
  | EMem   of mem_kind * (static_exp * static_exp * string option) * netlist_exp list
      (* ro * address size * word size * input file * args *)

and netlist_exp = netlist_exp_desc netlist_typed


type lvalue_desc =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

and lvalue = lvalue_desc localized


type equation_desc = {
  eq_left: lvalue;
  eq_right: netlist_exp
}
and equation = equation_desc localized


type block_desc =
    | BEqs of equation list
    | BIf  of static_exp * block * block

and block = block_desc localized


type inline_status = Inline | NotInline


type node_desc = {
  (* node_name:    ident; *)
  node_params : ident list;
  node_inputs : ident list;
  node_outputs: ident list;
  node_static_vars: static_exp Env.t;
  node_netlist_vars: netlist_exp Env.t;
  node_body:    block;
  (* n_constraints : static_exp list; *)
  node_inline:  inline_status;
  node_probes:  ident list;
}
and node = node_desc localized
and nodes = node Env.t


and consts = {
  const_values: static_exp Env.t;
  const_idents: Location.location Env.t;
  const_decls: Location.location Env.t
}

type program = {
  p_consts: consts;
  p_nodes : node list;
}

end *)
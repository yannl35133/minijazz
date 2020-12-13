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

type t = {
  i_id : int;
  i_name : string;
  i_loc: Location.location
}

let compare i1 i2 = compare i1.i_id i2.i_id

let string_of_ident id = id.i_name^"_"^(string_of_int id.i_id)

let print_ident ff id =
  Format.fprintf ff "%s" (string_of_ident id)

let dprint_ident id ff = print_ident ff id

module StringEnv = Map.Make (struct type t = string
                                    let compare = String.compare end)

let ident_counter = ref 0
let fresh_ident loc s =
  incr ident_counter;
  { i_id = !ident_counter; i_name = s; i_loc = loc }

let copy id =
  fresh_ident id.i_loc (string_of_ident id)

let symbol_table = ref StringEnv.empty
let reset_symbol_table () =
  symbol_table := StringEnv.empty
let ident_of_string s =
  if StringEnv.mem s !symbol_table then
    StringEnv.find s !symbol_table
  else (
    let id = fresh_ident Location.no_location s in
    symbol_table := StringEnv.add s id !symbol_table;
    id
  )

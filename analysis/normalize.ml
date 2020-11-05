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

open Ast
open Mapfold

let mk_eq e =
  let id = Ident.fresh_ident "_l" in
  let eq = (Evarpat id, e) in
  let vd = mk_var_dec id e.e_ty in
  Evar id, vd, eq

(* Put all the arguments in separate equations *)
let exp funs (eqs, vds) e = match !!e with
  | Econst _ | Evar _ -> e, (eqs, vds)
  | _ ->
      let e, (eqs, vds) = Mapfold.exp funs (eqs, vds) e in
      let desc, vd, eq = mk_eq e in
      { e with e_desc = desc }, (eq::eqs, vd::vds)

let equation funs (eqs, vds) (pat, e) =
  match !!e with
    | Econst _ | Evar _ -> (pat, e), (eqs, vds)
    | _ -> (
      match Mapfold.exp_it funs (eqs, vds) e with
      | _, ((_, e)::eqs, _::vds) -> (pat, e), (eqs, vds)
      | _ -> failwith "Mapfold.exp_it error"
    )
        

let block funs acc b = match b with
  | BEqs(eqs, vds) ->
      let eqs, (new_eqs, new_vds) = Misc.mapfold (Mapfold.equation_it funs) ([], []) eqs in
      BEqs(new_eqs@eqs, new_vds@vds), acc
  | BIf _ -> raise Mapfold.Fallback

let program p =
  let funs = { Mapfold.defaults with exp = exp; equation = equation; block = block } in
  let p, _ = Mapfold.program_it funs ([], []) p in
  p

(* Used by Callgraph *)
let block b =
  let funs = { Mapfold.defaults with exp = exp; equation = equation; block = block } in
  let b, _ = Mapfold.block_it funs ([], []) b in
  b

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
open ParserAST

(** verify all names are well defined
    merge all ident to unique id *)

module NameEnv = Map.Make (struct type t = string
                               let compare = String.compare end)

let scope_error (id:ident) =
  Format.eprintf "%aError: unknown variable %s.@."
    Location.print_location id.i_loc id.i_name;
  raise Errors.ErrorDetected

let duplicate_error kind (id:ident) =
  Format.eprintf "%aError: duplicate %s name: %s.@."
    Location.print_location id.i_loc kind id.i_name;
  raise Errors.ErrorDetected

(* static *)

let rec check_st_exp_desc s e = match e with
  | SInt _ | SBool _ -> e
  | SIdent id -> (try SIdent (NameEnv.find id.i_name s)
                 with Not_found -> scope_error id)
  | SPar e -> check_st_exp_desc s e.desc
  | SUnOp (op, e) -> SUnOp (op, check_st_exp s e)
  | SBinOp (op, e1, e2) -> SBinOp (op, check_st_exp s e1, check_st_exp s e2)
  | SIf (guard, e1, e2) -> SIf (check_st_exp s guard,
                               check_st_exp s e1, check_st_exp s e2)

and check_st_exp s e = relocalize !@e @@ check_st_exp_desc s !!e

let check_opt_st_exp s opt = match !!opt with
  | Some e -> relocalize !@opt @@ Some (check_st_exp_desc s e)
  | None -> opt

let check_slice s = function
  | SliceOne e -> SliceOne (check_opt_st_exp s e)
  | SliceFrom e -> SliceFrom (check_opt_st_exp s e)
  | SliceTo e -> SliceTo (check_opt_st_exp s e)
  | Slice (e1, e2) -> Slice (check_opt_st_exp s e1, check_opt_st_exp s e2)
  | e -> e

(* expressions *)

let rec check_exp_desc ((s, c, d) as env) e = match e with
  | EConst _ -> e
  | EConstr (Estate0 id) -> (try EConstr (Estate0 (NameEnv.find id.i_name c))
                            with Not_found -> scope_error id)
  | EConstr _ -> assert false
  | EVar id -> (try EVar (NameEnv.find id.i_name d)
               with Not_found -> scope_error id)
  | EPar e -> check_exp_desc env !!e
  | EReg e -> EReg (check_exp env e)
  | ESupOp (op, es) -> ESupOp (op, List.map (check_exp env) es)
  | ESlice (ps, e) -> ESlice (List.map (check_slice s) ps, check_exp env e)
  | ECall (func, ps, es) -> ECall (func, List.map (check_opt_st_exp s) ps,
                                  List.map (check_exp env) es)
  | EMem (kd, (addr_size, word_size, fname), args) ->
     EMem (kd, (check_opt_st_exp s addr_size,
                check_opt_st_exp s word_size,
                fname),
           List.map (check_exp env) args)
  | ELet _ -> assert false
  | EMerge _ -> assert false
  | EMatch _ -> assert false

and check_exp env e = relocalize !@e @@ check_exp_desc env !!e

(* equation/block *)

let rec insert_lvalue ((s,c,d) as env) lv = match lv.desc with
  | LValDrop -> env
  | LValId id -> s, c, NameEnv.add id.i_name id d
  | LValTuple ids -> List.fold_left insert_lvalue env ids

let filter_eq (env) d = match !!d with
  | Deq (lv, _) -> insert_lvalue env lv
  | _ -> env

let insert_state (s,c,d) hdl = match !!(hdl.s_state) with
  | Estate0pat id | Estatenpat (id, _) -> s, NameEnv.add id.i_name id c, d

let rec check_escape ((_,c,_) as env) e =
  let e_cond = check_exp env e.e_cond in
  let e_body = check_decl env e.e_body in
  let e_nx_state = match e.e_nx_state with
    | Estate0 id -> (try Estate0 (NameEnv.find id.i_name c)
                    with Not_found -> scope_error id)
    | Estaten (id, es) ->
       try Estaten (NameEnv.find id.i_name c, List.map (check_exp env) es)
       with Not_found -> scope_error id
  in
  { e with e_cond; e_body; e_nx_state }

and check_hdl (s,c,d) hdl =
  let d = List.fold_left
            (fun d (v:ident) -> NameEnv.add v.i_name v d) d hdl.s_vars in
  let env = s, c, d in
  let s_body = check_decl env hdl.s_body in
  let s_until = List.map (check_escape env) hdl.s_until in
  let s_unless = List.map (check_escape env) hdl.s_unless in
  { hdl with s_body; s_until; s_unless }

and check_decl_desc ((s,_,_) as env) de = match de with
  | Dempty -> de
  | Deq (lv, e) -> Deq (lv, check_exp env e)
  | Dand ds ->
     let env = List.fold_left filter_eq env ds in
     Dand (List.map (check_decl env) ds)
  | Dif (guard, b1, b2) ->
     Dif (check_st_exp s guard, check_decl env b1, check_decl env b2)
  | Dlet _ -> (* remove ? *) assert false
  | Dreset (d, e) -> Dreset (check_decl env d, check_exp env e)
  | Dautomaton hdls ->
     let env = List.fold_left insert_state env hdls in
     Dautomaton (List.map (check_hdl env) hdls)

and check_decl env d = relocalize !@d @@ check_decl_desc env !!d

(* shortcut to build set from list
   raise error if insert duplicates *)

let build kind (f: 'a -> ident) lst env =
  List.fold_left (fun s c -> if NameEnv.mem (f c).i_name s
                            then duplicate_error kind (f c)
                            else NameEnv.add (f c).i_name (f c) s) env lst

(* check program names *)
let check_names p =
  (* global env *)
  let s = build "constant" (fun c -> c.const_left) p.p_consts NameEnv.empty in
  let d = build "node" (fun n -> n.node_name) p.p_nodes NameEnv.empty in

  (* check doubles enum name *)
  let _ = build "enum" (fun e -> e.enum_name) p.p_enums NameEnv.empty in

  let c_lst = List.concat (List.map (fun e -> e.enum_pats) p.p_enums) in
  let c = build "constructor" (fun x -> x) c_lst NameEnv.empty in

  let node n =
    let s = build "parameter" (fun p -> p.st_name) n.node_params s in
    let d = build "input" (fun i -> i.name) n.node_inputs d in
    { n with node_body = check_decl (s, c, d) n.node_body }
  in

  { p with p_nodes = List.map node p.p_nodes }

(* TODO: add expression simplifications ? *)
let program = check_names

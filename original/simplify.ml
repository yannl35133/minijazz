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

open Ast_old
open Static

let debug = 0
let log i =
  if debug >= i then
    Format.printf
  else
    Format.ifprintf Format.std_formatter

let equal_values = function
  | VBit b, VBit b'
  | VBitArray [| b |], VBit b'
  | VBit b, VBitArray [| b' |] -> b = b'
  | VBitArray a, VBitArray a' -> Array.length a = Array.length a' && Array.for_all2 (=) a a'
  | _ -> false

let rec equal_static_expressions = function
  | SInt n, SInt n' -> n = n'
  | SBool b, SBool b' -> b = b'
  | SVar id, SVar id' -> id = id'
  | SBinOp (op, se1, se2), SBinOp (op', se1', se2') ->
      op = op' &&
        equal_static_expressions (se1.se_desc, se1'.se_desc) &&
        equal_static_expressions (se2.se_desc, se2'.se_desc)
  | SIf (c, se1, se2), SIf (c', se1', se2') ->
      equal_static_expressions (c.se_desc, c'.se_desc) &&
        equal_static_expressions (se1.se_desc, se1'.se_desc) &&
        equal_static_expressions (se2.se_desc, se2'.se_desc)
  | _ -> false

let rec equal_expressions = function
  | Econst v, Econst v' -> equal_values (v, v')
  | Evar id, Evar id' -> id.i_id = id'.i_id
  | Ereg e, Ereg e' -> equal_expressions (e.e_desc, e'.e_desc)
  | Ecall (fname, params, exps), Ecall (fname', params', exps') ->
      fname = fname' &&
        List.for_all Fun.id @@ List.map equal_static_expressions @@ List.combine (List.map (fun e -> e.se_desc) params) (List.map (fun e -> e.se_desc) params') &&
        List.for_all Fun.id @@ List.map equal_expressions @@ List.combine (List.map (fun e -> e.e_desc) exps) (List.map (fun e -> e.e_desc) exps')
      (* function * params * args *)
  | Emem _, _ | _, Emem _ -> false
  | _ -> false

let rec subst (id1: ident) id2 =
  (fun f e -> { e with e_desc = f e.e_desc}) @@
  function
  | Econst v -> Econst v
  | Evar id -> if id.i_id = id1.i_id then Evar id2 else Evar id
  | Ereg e -> Ereg (subst id1 id2 e)
  | Ecall (fname, params, exps) ->
      Ecall (fname, params, List.map (subst id1 id2) exps)
  | Emem (mem, p1, p2, p3, exps) -> Emem (mem, p1, p2, p3, List.map (subst id1 id2) exps)

let is_not_zero ty = match ty with
  | TBitArray { se_desc = SInt 0; _ } -> false
  | _ -> true

let rec simplify_exp e = match e.e_desc with
  (* replace x[i..j] with [] if j < i *)
  | Ecall("slice",
         [{ se_desc = SInt min; _ };
          { se_desc = SInt max; _ }; _n], _) when max < min ->
      { e with e_desc = Econst (VBitArray (Array.make 0 false)) }
  (* replace x[i..i] with x[i] *)
  | Ecall("slice", [min; max; n], args) when min = max ->
      let new_e = { e with e_desc = Ecall("select", [min; n], args) } in
      simplify_exp new_e
  (* replace x.[] or [].x with x *)
  | Ecall("concat", _, [{ e_ty = TBitArray { se_desc = SInt 0; _ }; _ }; e1])
  | Ecall("concat", _, [e1; { e_ty = TBitArray { se_desc = SInt 0; _ }; _ }]) ->
      e1
  | Ecall(f, params, args) ->
      { e with e_desc = Ecall(f, params, List.map simplify_exp args) }
  | _ -> e

let simplify_eq (pat,e) =
  (pat, simplify_exp e)

(* let find_duplicates (id, exp) eqs =
  let dups, keeps = List.partition (fun (_, exp') -> equal_expressions (exp.e_desc, exp'.e_desc)) eqs in
  let dups_ids = List.map (function
    | Evarpat id, _ -> id
    | Etuplepat ids, _ -> Format.eprintf "Unexpected pattern: %a@." Printer.print_pat (Etuplepat ids); assert false
    ) dups in
  let eqs = List.fold_left (fun eqs id' -> List.map (fun (a, b) -> a, subst id' id b) eqs) keeps dups_ids in
  (Evarpat id, exp) :: eqs, dups_ids

let find_trivials eqs =
  let trivials, keeps = List.partition (function (_, {e_desc=Evar id';_}) -> true | _ -> false) eqs in
  let trivials_ids = List.map (function
    | Evarpat id, {e_desc=Evar id';_} -> (id', id)
    | _ -> assert false
    ) trivials in
  let eqs = List.fold_left (fun eqs (id', id) -> List.map (fun (a, b) -> a, subst id' id b) eqs) keeps trivials_ids in
  eqs, List.map snd trivials_ids *)

let rec find_duplicates i j k removed acc = function
  | (Etuplepat _ids, _) :: _ -> Format.eprintf "Unexpected pattern: %a@." Printer.print_pat (Etuplepat _ids); assert false
  | (Evarpat id, { e_desc = Evar id'; _ }) :: tl ->
      log 2 "%i, %i, %i remove %a for %a@." j i k Ident.print_ident id' Ident.print_ident id;
      let subst_list = List.map (fun (p, e) -> p, subst id' id e) in
      find_duplicates 0 (j+1) (k+1) (id'.i_id :: removed) (subst_list acc) (subst_list tl)
  | (Evarpat id, exp) :: (Evarpat id', exp') :: tl when equal_expressions (exp.e_desc, exp'.e_desc) ->
      log 2 "%i, %i, %i remove %a for %a@." j i k Ident.print_ident id' Ident.print_ident id;
      let subst_list = List.map (fun (p, e) -> p, subst id' id e) in
      find_duplicates 0 (j+1) (k+1) (id'.i_id :: removed) (subst_list acc) (subst_list ((Evarpat id, exp) :: tl))
  | hd :: tl ->
      log 2 "%i, %i, %i@." j i k;
      find_duplicates (i+1) j (k+1) removed (hd :: acc) tl
  | [] ->
      log 1 "%i, %i, %i fini@." j i k;
      removed, acc

let rec depends_on (id: ident) e = match e.e_desc with
  | Econst _ -> false
  | Evar id' -> id.i_id = id'.i_id
  | Ereg e -> depends_on id e
  | Ecall (_, _, l) | Emem (_, _, _, _, l) -> List.exists (depends_on id) l


let is_useless (id: ident) eqs =
  let (neqs, eqs') = List.partition (function (Etuplepat _, _) -> assert false | Evarpat id', _ -> id.i_id = id'.i_id) eqs in
  let exps = List.map snd neqs in
  let e_desc = match exps with
  | [exp] -> exp.e_desc
  | [] -> Econst (VBit false)
  | _ -> assert false
  in
  match e_desc with
  | Ecall ("slice", min::_max::_, e) ->
      let useless = ref true in
      let eqs' = List.map (function
      | (pat, {e_desc=Ecall ("slice", min'::max'::r, [{e_desc=Evar id'; _}]); e_ty; e_loc}) when id.i_id = id'.i_id ->
          (pat, {e_desc=Ecall ("slice", {se_desc=SBinOp(SAdd, min, min');se_loc=Location.no_location} :: max' :: r, e); e_ty; e_loc})
      | (pat, {e_desc=Ecall ("select", idx::r, [{e_desc=Evar id'; _}]); e_ty; e_loc}) when id.i_id = id'.i_id ->
          (pat, {e_desc=Ecall ("select", {se_desc=SBinOp(SAdd, min, idx);se_loc=Location.no_location} :: r, e); e_ty; e_loc})
      | (_, e) as eq when depends_on id e -> useless := false; eq
      | eq -> eq
      ) eqs' in
      eqs', !useless
  | _ ->
      eqs, false

let remove_useless (eqs, vds) =
  List.fold_left (fun (i, j, k, eqs, vds) v ->
    let eqs', useless = is_useless v.v_ident eqs in
    if useless then begin
      log 2 "%i, %i, %i useless %s@." i j k v.v_ident.i_name;
      (i+1), 0, (k+1), eqs', List.filter (fun v' -> v'.v_ident.i_id <> v.v_ident.i_id) vds
    end else begin
      log 2 "%i, %i, %i@." i j k;
      i, j+1, k+1, eqs, vds
    end
    ) (0,0,0,eqs, vds) vds

let rec remove_duplicates (eqs, vds) =
  (* Format.eprintf "@.%a@." (Printer.print_list_nlr Printer.print_var_dec "" ", " "") vds; *)
  (* let removed, eqs = find_duplicates 0 0 0 [] [] (List.sort (fun (_, a) (_, b) -> compare a.e_desc b.e_desc) eqs) in *)
  (* Printer.print_list_nlr Format.pp_print_int "" ", " "" Format.err_formatter removed; *)
  (* if removed <> [] then *)
    (* let vds, vds' = List.partition (fun v -> not @@ List.exists (fun uid -> uid = v.v_ident.i_id) removed) vds in *)
    (* Format.eprintf "@.%a@.@." (Printer.print_list_nlr Printer.print_var_dec "" ", " "") vds'; *)
    (* remove_duplicates (eqs, vds) *)
  (* else *)
    remove_useless (eqs, vds)

let rec block b = match b with
  | BEqs(eqs, vds) ->
      let eqs = List.map simplify_eq eqs in
      (* remove variables with size 0 *)
      let vds = List.filter (fun vd -> is_not_zero vd.v_ty) vds in
      let eqs = List.filter (fun (_, e) -> is_not_zero e.e_ty) eqs in

      (* let _,_,_,eqs, vds = remove_duplicates (eqs, vds) in *)

      BEqs(eqs, vds)
  | BIf(se, trueb, elseb) -> BIf(se, block trueb, block elseb)

let node n =
  { n with n_body = block n.n_body }

let program p =
    { p with p_nodes = List.map node p.p_nodes }

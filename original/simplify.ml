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

let rec find_duplicates removed acc = function
  | (pat, exp) :: (pat', exp') :: tl when equal_expressions (exp.e_desc, exp'.e_desc) ->
    let tr_pat pat = match pat with
      | Evarpat id -> id
      | Etuplepat _ids ->
          Format.eprintf "Unexpected pattern: %a@." Printer.print_pat pat;
          assert false
    in
    find_duplicates (tr_pat pat' :: removed) [] @@ List.map (fun (p, e) -> p, subst (tr_pat pat') (tr_pat pat) e) @@ List.rev_append acc ((pat, exp) :: tl)
  | hd :: tl -> find_duplicates removed (hd :: acc) tl
  | [] -> removed, acc

let rec remove_duplicates (eqs, vds) =
  let removed, eqs = find_duplicates [] [] (List.sort (fun (_, a) (_, b) -> compare a.e_desc b.e_desc) eqs) in
  if removed <> [] then
    let vds = List.filter (fun v -> List.mem v.v_ident removed) vds in
    remove_duplicates (eqs, vds)
  else
    (eqs, vds)

let rec block b = match b with
  | BEqs(eqs, vds) ->
      let eqs = List.map simplify_eq eqs in
      (* remove variables with size 0 *)
      let vds = List.filter (fun vd -> is_not_zero vd.v_ty) vds in
      let eqs = List.filter (fun (_, e) -> is_not_zero e.e_ty) eqs in

      let eqs, vds = remove_duplicates (eqs, vds) in

      BEqs(eqs, vds)
  | BIf(se, trueb, elseb) -> BIf(se, block trueb, block elseb)

let node n =
  { n with n_body = block n.n_body }

let program p =
    { p with p_nodes = List.map node p.p_nodes }

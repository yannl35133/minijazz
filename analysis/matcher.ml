open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

module M = Map.Make(struct
  type t = lvalue

  let rec fold lvs1 lvs2 = match lvs1, lvs2 with
    | [], [] -> -1
    | [], _ | _, [] -> -1
    | lv1 :: lvs1, lv2 :: lvs2 ->
      match compare lv1 lv2 with
      | 0 -> fold lvs1 lvs2
      | n -> n

  and compare lv1 lv2 = match lv1.b_desc, lv2.b_desc with
    | LValId id1, LValId id2 ->
      UIDIdent.compare id1.id_uid id2.id_uid
    | LValTuple lvs1, LValTuple lvs2 -> fold lvs1 lvs2
    | _ -> -1
end)

module I = Map.Make(Int)

(* one bit encoding of enum *)
let build f lst = List.fold_left f ConstructEnv.empty lst

let rec gen_lv prefix (lv:lvalue) =
  let uid = UIDIdent.get () in
  match lv.b_desc with
  | LValDrop -> [None]
  | LValId id ->
     let ident = { id_uid  = uid;
                   id_desc = prefix ^ id.id_desc ^ (UIDIdent.to_string uid);
                   id_loc  = id.id_loc } in
     let lvvar, var = match lv.b_type with
       | BNetlist sz ->
          Exp (size (EVar id) id.id_loc sz),
          Exp (size (EVar ident) id.id_loc sz)
       | BState st ->
          StateExp (state_type (ESVar id) id.id_loc st),
          StateExp (state_type (ESVar ident) id.id_loc st)
       | BStateTransition _ -> assert false in
     [Some (lv, lvvar, tritype (LValId ident) id.id_loc lv.b_type, var)]
  | LValTuple lvs -> List.concat_map (gen_lv prefix) lvs

let mux (e:exp) (e1:tritype_exp) e2 = match e1, e2 with
  | Exp e1, Exp e2 ->
     Exp { e1 with si_desc = ECall (relocalize e.si_loc "mux", [], [e; e1; e2])}
  | StateExp e1, StateExp e2 ->
     StateExp { e1 with s_desc = ESMux (e, e1, e2) }
  | _ -> assert false

let emux e e1 e2 =
  { e1 with si_desc = ECall (relocalize e.si_loc "mux", [], [e; e1; e2])}

let ereg e = { e with si_desc = EReg e }

let reg (e:tritype_exp) = match e with
  | Exp e -> Exp { e with si_desc = EReg e }
  | StateExp e -> StateExp { e with s_desc = ESReg e }
  | StateTransitionExp _ -> assert false

let id_to_var ty id =
  let sz = match ty with
    | BNetlist sz -> sz
    | _ -> assert false in
  size (EVar id) id.id_loc sz

let one =
  size (EConst (VBit true)) (Location.no_location) (TNDim [Size (SInt 1)])

let eand e1 e2 =
  { e1 with si_desc = ECall (relocalize e1.si_loc "and", [], [e1;e2])}

let slice e i =
  let n = match e.si_size with
    | TNDim [Size n] -> relocalize e.si_loc @@ SIntExp n
    | _ -> assert false
  in
  let i = relocalize e.si_loc @@ SIntExp (SInt i) in
  { e with si_desc = ECall (relocalize e.si_loc "slice_one", [n; i], [e])}

let enum_tbl : (UIDIdent.t, int) Hashtbl.t = Hashtbl.create 16
let constr_tbl : (UIDConstructor.t, int) Hashtbl.t = Hashtbl.create 16

let enum_size (e:enum) = Hashtbl.find enum_tbl e.enum_name.id_uid
let index c = Hashtbl.find constr_tbl c

let program_nodes_tbl : (UIDIdent.t, node) Hashtbl.t = Hashtbl.create 16

let inter e1 e2 =
  Env.fold (fun uid v e -> if Env.mem uid e2 then Env.add uid v e else e)
    e1 Env.empty

let remove e1 e2 =
  Env.fold (fun uid _ e -> if Env.mem uid e2 then Env.remove uid e else e)
    e1 e2

let union e1 e2 = Env.union (fun _uid v1 _v2 -> Some v1) e1 e2

(* free variables *)
let rec state_exp (sfv, fv) (e:exp state_exp) =
  let ty_sz = enum_size e.s_type in
  let ty = TNDim [Size (SInt ty_sz)] in
  let sfv, fv, desc = match e.s_desc with
    | ESConstr c ->
       let i = index c.id_uid in
       sfv, fv, EConst (VNDim (List.init ty_sz (fun j -> VBit (i = j))))
    | ESVar v ->
       let ti = { ti_name = v;
                  ti_type = relocalize v.id_loc @@ BNetlist ty;
                  ti_loc = e.s_loc } in
       sfv, Env.add v.id_uid ti fv, EVar v
    | ESReg e -> let sfv, fv, e = state_exp (sfv, fv) e in sfv, fv, EReg e
    | ESMux (ce, e1, e2) ->
       let sfv, fv, e1 = state_exp (sfv, fv) e1 in
       let sfv, fv, e2 = state_exp (sfv, fv) e2 in
       let sfv, fv = exp (sfv, fv) ce in
       sfv, fv, ECall (relocalize e.s_loc "mux", [], [ce; e1; e2])
  in
  sfv, fv, size desc e.s_loc ty

and exp (sfv, fv) (e:exp) = match e.si_desc with
  | EConst _ -> sfv, fv
  | EVar v ->
     let ti = { ti_name = v;
                ti_type = relocalize e.si_loc @@ BNetlist e.si_size;
                ti_loc = e.si_loc } in
     sfv, Env.add v.id_uid ti fv
  | EReg e -> exp (sfv, fv) e
  | ECall (_, ps, args) -> List.fold_left static_exp
                          (List.fold_left exp (sfv, fv) args) ps
  | EMem (_, (s1, s2, _), args) ->
     List.fold_left exp (static_int_exp (static_int_exp (sfv, fv) !!s2) !!s1) args

and static_exp acc (se:static_bitype_exp) = match se.desc with
  | SIntExp si -> static_int_exp acc si
  | SBoolExp sb -> static_bool_exp acc sb

and static_int_exp ((sfv, fv) as acc) e = match e with
  | SInt _ -> acc
  | SIParam id ->
     let sti =
       { sti_name = id;
         sti_type = relocalize id.id_loc TInt;
         sti_loc = id.id_loc } in
     I.add id.id_uid sti sfv, fv
  | SIConst _ -> acc
  | SIUnOp (_, e) -> static_int_exp acc !!e
  | SIBinOp (_, e1, e2) -> static_int_exp (static_int_exp acc !!e1) !!e2
  | SIIf (e, e1, e2) ->
     static_int_exp (static_int_exp (static_bool_exp acc e.desc) !!e1) !!e2

and static_bool_exp ((sfv, fv) as acc) e = match e with
  | SBool _ -> acc
  | SBParam id ->
     let sti =
       { sti_name = id;
         sti_type = relocalize id.id_loc TInt;
         sti_loc = id.id_loc } in
     I.add id.id_uid sti sfv, fv
  | SBConst _ -> acc
  | SBUnOp (_, e) -> static_bool_exp acc !!e
  | SBBinOp (_, e1, e2) -> static_bool_exp (static_bool_exp acc !!e1) !!e2
  | SBBinIntOp (_, e1, e2) -> static_int_exp (static_int_exp acc !!e1) !!e2
  | SBIf (e, e1, e2) ->
     static_bool_exp (static_bool_exp (static_bool_exp acc e.desc) !!e1) !!e2

and lv_to_output env (lv:lvalue) = match lv.b_desc with
  | LValDrop -> env
  | LValId id ->
     let ti = { ti_name = id;
                ti_type = relocalize lv.b_loc lv.b_type;
                ti_loc = lv.b_loc } in
     Env.add id.id_uid ti env
  | LValTuple lvs -> List.fold_left lv_to_output env lvs

(*****)

let env_to_list (env:exp M.t) =
  M.fold (fun lv exp b -> (relocalize lv.b_loc @@ Deq (lv, Exp exp)) :: b)
    env []

let list_to_env (b: decl list) =
  List.fold_left (fun env d ->
      match d.desc with
      | Deq (lv, Exp exp) -> M.add lv exp env
      | _ -> assert false) M.empty b

let rec rename_lv px (env: ident Env.t) (lv:lvalue) =
  let env, b_desc = match lv.b_desc with
    | LValDrop -> env, lv.b_desc
    | LValId id ->
       let nid = { id with
                   id_uid  = UIDIdent.get ();
                   id_desc = px ^ id.id_desc } in
       Env.add id.id_uid nid env, LValId nid
    | LValTuple lvs ->
       let env, lvs =
         List.fold_left (fun (env, lvs) lv ->
             let env, lv = rename_lv px env lv in
             env, lv :: lvs) (env, []) lvs in
       env, LValTuple (List.rev lvs)
  in
  env, { lv with b_desc }

and mux_lv cond defs b lv new_lv : exp M.t =
  match lv.b_desc, new_lv.b_desc with
  | LValDrop, LValDrop -> b
  | LValId id, LValId nid ->
     let var = id_to_var lv.b_type nid in
     begin match Env.find_opt id.id_uid defs with
     | None -> M.add lv var b
     | Some id2 -> M.add lv (emux cond var (id_to_var lv.b_type id2)) b
     end
  | LValTuple lvs, LValTuple new_lvs ->
     List.fold_left2 (mux_lv cond defs) b lvs new_lvs
  | _ -> assert false

let rec ti_to_lv (szs, lvs) t =
  match (t.ti_type).desc with
  | BNetlist ty ->
     ty :: szs,
     (tritype (LValId (t.ti_name)) t.ti_loc t.ti_type.desc) :: lvs
  | _ -> assert false

and sti_to_stbitype t = match t.sti_type.desc with
  | TInt -> relocalize t.sti_loc @@ SIntExp (SIParam t.sti_name)
  | TBool -> relocalize t.sti_loc @@ SBoolExp (SBParam t.sti_name)

and ti_to_exp t = match (t.ti_type).desc with
  | BNetlist ty -> size (EVar t.ti_name) t.ti_loc ty
  | BState _ -> assert false
  | BStateTransition _ -> assert false

and node_of_block_global n =
  let node_body, _, _, _ =
    List.fold_left (decl n.node_name.desc Env.empty)
      ([], I.empty, Env.empty, Env.empty) n.node_body in
  Hashtbl.replace program_nodes_tbl (UIDIdent.get ())
    { n with node_body }

and node_of_block px env loc ds =
  let node_body, node_params, node_inputs, node_outputs =
    List.fold_left (decl px env) ([], I.empty, Env.empty, Env.empty) ds in
  let node : node = {
      node_name = relocalize loc px;
      node_loc  = loc;
      node_params = I.fold (fun _ p lst -> p :: lst) node_params [];
      node_inline = NotInline;
      node_inputs = Env.fold (fun _ p lst -> p :: lst) node_inputs [];
      node_outputs = Env.fold (fun _ p lst -> p :: lst) node_outputs [];
      node_body;
      node_variables = Env.empty
    } in
  Hashtbl.replace program_nodes_tbl (UIDIdent.get ()) node;
  let sz, lvs = List.fold_left ti_to_lv ([], []) node.node_outputs in
  let ps = List.map sti_to_stbitype node.node_params in
  let args = List.map ti_to_exp node.node_inputs in
  tritype (LValTuple lvs) loc (BNetlist (TProd sz)),
  size (ECall (node.node_name, ps, args)) loc (TProd sz),
  node_params, node_inputs, node_outputs


and decl px env (b, p, i, o) (d:decl) = match d.desc with
  | Dmatch (e, m) ->
     let p, i, e = state_exp (p, i) e in
     let _lvs, b, _, p, i, o =
       ConstructEnv.fold
         (fun c h (lvs, b, defs, _p, _i, _o) ->
           let px = px ^ h.m_state.id_desc in
           let lv, exp, p, i, o =
              node_of_block px env h.m_hloc h.m_body in
           let new_defs, new_lv = rename_lv px defs lv in
           let cond = slice e (index c) in
           let b = mux_lv cond defs b lv new_lv in
           lv :: lvs,
           M.add new_lv exp b,
           new_defs, p, i, o)
         m.m_handlers ([], list_to_env b, Env.empty, p, i, o)
     in
     (* TODO enable *)
     env_to_list b, p, i, o

  | Deq ({ b_desc = LValDrop; _ }, _) -> b, p, i, o
  | Deq (lv, Exp e) ->
     let p, i = exp (p, i) e in
     d :: b, p, i, lv_to_output o lv
  | Deq (lv, StateExp e) ->
     let p, i, e = state_exp (p, i) e in
     let lv = { lv with b_type = BNetlist e.si_size } in
     let eq = Deq (lv, Exp e) in
     relocalize d.loc eq :: b, p, i, lv_to_output o lv
  | Deq (_, StateTransitionExp _) -> assert false

  | Dif (c, b1, b2) ->
     let p, i = static_bool_exp (p, i) !!c in
     let b1, p, i1, o1 = List.fold_left (decl px env) ([], p, i, o) b1 in
     let b2, p, i2, o2 = List.fold_left (decl px env) ([], p, i, o) b2 in
     [relocalize d.loc @@ Dif (c, b1, b2)], p,
     union i1 i2, inter o1 o2 (* TODO probably incorrect or useless *)

  (* can't occur *)
  | Dreset (_, _) -> assert false
  | Dlocaleq (_, _) -> assert false
  | Dautomaton _ -> assert false

(** enable
    must be done __after__ removing state expressions *)

let bit_type = TNDim [Size (SInt 1)]

let new_en_var _ =
  let uid = UIDIdent.get () in
  let id = { id_uid = uid; id_loc = Location.no_location;
             id_desc = "en" ^ (UIDIdent.to_string uid )} in
  id, size (EVar id) Location.no_location bit_type

let is_native_fname s =
  let regex = Str.regexp {|\(or\|and\|xor\|nand\|nor\|not\|mux\)_\([01]\)|} in
  Str.string_match regex s 0

let rec en_exp en (e:tritype_exp) = match e with
  | Exp e -> Exp (en_exp' en e)
  | StateExp se -> StateExp (en_sexp en se)
  | StateTransitionExp _ -> assert false

and en_exp_desc en (e:exp_desc) = match e with
  | EConst _ -> e
  | EVar _ -> e
  | EReg e -> EReg (en_exp' en e)
  | EMem (st1, st2, es) -> EMem (st1, st2, List.map (en_exp' en) es)
  | ECall ({ desc = fname; _ }, _, _) when is_native_fname fname -> e
  | ECall ({ desc = "slice_one"; _ }, _, _)
    | ECall ({ desc = "slice_all"; _ }, _, _)
    | ECall ({ desc = "slice_from"; _ }, _, _)
    | ECall ({ desc = "slice_to"; _ }, _, _)
    | ECall ({ desc = "slice_fromto"; _ }, _, _)
    | ECall ({ desc = "add_dim_0"; _ }, _, _)
    | ECall ({ desc = "concat_1"; _ }, _, _)  -> e
  | ECall (fname, ps, args) ->
     ECall (fname, ps, en :: List.map (en_exp' en) args)

and en_exp' en e = size (en_exp_desc en e.si_desc) e.si_loc e.si_size

and en_sexp_desc en (e:exp state_exp_desc) = match e with
  | ESConstr _ -> e
  | ESVar _ -> e
  | ESReg e -> ESReg (en_sexp en e)
  | ESMux (e, se1, se2) -> ESMux (en_exp' en e, en_sexp en se1, en_sexp en se2)

and en_sexp en (e:exp state_exp) = re_state_type e (en_sexp_desc en e.s_desc)

and en_decl en (d:decl) = match d.desc with
  | Deq ({ b_desc = LValDrop; _ }, _) -> []
  | Deq (lv, e) ->
     let lst = gen_lv "tmp" lv in
     let lst_lv, lst_eq =
       List.fold_right (fun x (lst_lv, lst_eq)  ->
           match x with
           | Some (lv, var_lv, tmp_lv, tmp_var) ->
              let eq = Deq (lv, (mux en tmp_var (reg var_lv))) in
              tmp_lv :: lst_lv, (relocalize d.loc @@ eq) :: lst_eq
           | None -> (tritype LValDrop lv.b_loc lv.b_type) :: lst_lv, lst_eq)
         lst ([],[])
     in
     let tuple = tritype (LValTuple lst_lv) lv.b_loc lv.b_type in
     (relocalize d.loc @@ Deq (tuple, en_exp en e)):: lst_eq
  | Dif (sc, b1, b2) ->
     let b1 = List.concat_map (en_decl en) b1 in
     let b2 = List.concat_map (en_decl en) b2 in
     [relocalize d.loc @@ Dif (sc, b1, b2)]
  | Dmatch (e, m) ->
     let m_handlers =
       ConstructEnv.map
         (fun h -> { h with m_body = List.concat_map (en_decl en) h.m_body })
         m.m_handlers in
     [relocalize d.loc @@ Dmatch (en_sexp en e, { m with m_handlers })]

  | Dlocaleq (_, _) -> assert false
  | Dreset (_, _) -> assert false
  | Dautomaton _ -> assert false

let en_node (n:node) =
  let id, en = new_en_var () in
  let node_inputs = { ti_name = id;
                      ti_type = no_localize @@ BNetlist bit_type;
                      ti_loc = Location.no_location } :: n.node_inputs in
  let node_body = List.concat_map (en_decl en) n.node_body in

  { n with node_inputs; node_body }

(** [Matcher.program p] compiles match from a automaton-reset-free ast *)
let program (p:program) =
  ConstructEnv.iter (fun _ e ->
      let sz = List.length e.enum_constructors_names in
      Hashtbl.replace enum_tbl e.enum_name.id_uid sz;
      List.iteri (fun i c -> Hashtbl.replace constr_tbl c.id_uid i)
        e.enum_constructors_names)
    p.p_enums;
  FunEnv.iter (fun _ n -> node_of_block_global n) p.p_nodes;
  { p with
    p_enums = ConstructEnv.empty;
    p_nodes = Hashtbl.fold (fun _ node p_nodes ->
                  FunEnv.add node.node_name.desc node p_nodes)
                program_nodes_tbl FunEnv.empty }

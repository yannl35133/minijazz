open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let fmap f lst = List.flatten @@ List.map f lst

module M = Map.Make(struct
               type t = lvalue

               let rec fold lvs1 lvs2 = match lvs1, lvs2 with
                 | [], [] -> assert false
                 | [], _ | _, [] -> assert false
                 | lv1 :: lvs1, lv2 :: lvs2 ->
                    match compare lv1 lv2 with
                    | 0 -> fold lvs1 lvs2
                    | n -> n

               and compare lv1 lv2 = match lv1.b_desc, lv2.b_desc with
                 | LValId id1, LValId id2 ->
                    UIDIdent.compare id1.id_uid id2.id_uid
                 | LValTuple lvs1, LValTuple lvs2 -> fold lvs1 lvs2
                 | _ -> assert false
             end)

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
  | LValTuple lvs -> fmap (gen_lv prefix) lvs

let mux (e:exp) (e1:tritype_exp) e2 = match e1, e2 with
  | Exp e1, Exp e2 ->
     Exp { e1 with si_desc = ECall (relocalize e.si_loc "mux", [], [e; e1; e2])}
  | StateExp e1, StateExp e2 ->
     StateExp { e1 with s_desc = ESMux (e, e1, e2) }
  | _ -> assert false

let exp_mux e e1 e2 =
  { e1 with si_desc = ECall (relocalize e.si_loc "mux", [], [e; e1; e2])}

let reg (e:tritype_exp) = match e with
  | Exp e -> Exp { e with si_desc = EReg e }
  | StateExp e -> StateExp { e with s_desc = ESReg e }
  | StateTransitionExp _ -> assert false

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
let index c = Hashtbl.find constr_tbl c.id_uid

let union = M.union (fun _ _ _ -> assert false)

let rec exp (e:exp state_exp) =
  let ty_sz = enum_size e.s_type in
  let desc = match e.s_desc with
    | ESConstr c ->
       let i = index c in
       EConst (VNDim (List.init ty_sz (fun j -> VBit (i = j))))
    | ESVar v -> EVar v
    | ESReg e -> EReg (exp e)
    | ESMux (ce, e1, e2) ->
       ECall (relocalize e.s_loc "mux", [], [ce; exp e1; exp e2])
  in
  size desc e.s_loc (TNDim [Size (SInt ty_sz)])

and rename_lv (c:UIDConstructor.t) (env: ident Env.t) (lv:lvalue) =
  let env, b_desc = match lv.b_desc with
    | LValDrop -> env, lv.b_desc
    | LValId id ->
       let nid = { id with
                   id_uid  = UIDIdent.get ();
                   id_desc =  id.id_desc ^ (UIDConstructor.to_string c) } in
       Env.add id.id_uid nid env, LValId nid
    | LValTuple lvs ->
       let env, lvs =
         List.fold_left (fun (env, lvs) lv ->
             let env, lv = rename_lv c env lv in
             env, lv :: lvs) (env, []) lvs in
       env, LValTuple lvs
  in
  env, { lv with b_desc }

and decl env (d:decl) = match d.desc with
  | Dmatch (e, m) ->
     let _e = exp e in
     (* TODO enable *)
     (* c is block constructor, b is block equation lists
        acc_b is accumulated equation of the new block and
        defs maps original idents to new block names *)
     let merge c (b: exp M.t) ((acc_b, defs): exp M.t * ident Env.t) =
       Format.printf "Constructor %s@." (UIDConstructor.to_string c);
       M.fold (fun lv eq (acc_b, defs) ->
           let defs, lv = rename_lv c defs lv in
           M.add lv eq acc_b, defs)
         b (acc_b, defs)
     in

     (* recursive calls on handlers *)
     let map : exp M.t ConstructEnv.t =
       ConstructEnv.map
         (fun h ->
           List.fold_left
             (fun acc d -> union (decl env d) acc) M.empty h.m_body)
         m.m_handlers
     in
     let b, _defs = ConstructEnv.fold merge map (M.empty, Env.empty) in
     b (* defs ? *)

  | Deq ({ b_desc = LValDrop; _ }, _) -> env
  | Deq (lv, Exp e) -> M.add lv e env
  | Deq (lv, StateExp e) -> M.add lv (exp e) env
  | Deq (_, StateTransitionExp _) -> assert false

  | Dif (_c, _b1, _b2) -> assert false (* TODO *)

  (* can't occur *)
  | Dreset (_, _) -> assert false
  | Dlocaleq (_, _) -> assert false
  | Dautomaton _ -> assert false

let env2list env =
  M.fold (fun lv (e:exp) lst ->
      (relocalize e.si_loc @@ Deq (lv, Exp e)) :: lst) env []

let node (n:node) =
  let b = List.map (decl M.empty) n.node_body in
  let b = fmap env2list b in
  { n with node_body = b }

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
     let b1 = fmap (en_decl en) b1 in
     let b2 = fmap (en_decl en) b2 in
     [relocalize d.loc @@ Dif (sc, b1, b2)]
  | Dmatch (e, m) ->
     let m_handlers =
       ConstructEnv.map
         (fun h -> { h with m_body = fmap (en_decl en) h.m_body })
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
  let node_body = fmap (en_decl en) n.node_body in

  { n with node_inputs; node_body }

(** [Matcher.program p] compiles match from a automaton-reset-free ast *)
let program (p:program) =
  ConstructEnv.iter (fun _ e ->
      let sz = List.length e.enum_constructors_names in
      Hashtbl.replace enum_tbl e.enum_name.id_uid sz;
      List.iteri (fun i c -> Hashtbl.replace constr_tbl c.id_uid i)
        e.enum_constructors_names)
    p.p_enums;
  { p with p_nodes = FunEnv.map (fun n -> node n) p.p_nodes }

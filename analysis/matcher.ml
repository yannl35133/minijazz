open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let fmap f lst = List.flatten @@ List.map f lst

module M = Map.Make(struct type t = ident
                           let compare i1 i2 =
                             UIDIdent.compare i1.id_uid i2.id_uid
                    end)

(* one bit encoding of enum *)
let build f lst = List.fold_left f ConstructEnv.empty lst

let gen_lv prefix (e:NetlistSizedAST.tritype_exp) =
  let uid = UIDIdent.get () in
  match e with
  | Exp e ->
     let ident = { id_uid  = uid;
                   id_desc = prefix ^ (UIDIdent.to_string uid);
                   id_loc  = e.si_loc} in
     tritype (LValId ident) e.si_loc (BNetlist e.si_size),
     Exp (size (EVar ident) e.si_loc e.si_size)
  | StateExp e ->
     let ident = { id_uid  = uid;
                   id_desc = prefix ^ (UIDIdent.to_string uid);
                   id_loc  = e.s_loc} in
     tritype (LValId ident) e.s_loc (BState e.s_type),
     StateExp (state_type (ESVar ident) e.s_loc e.s_type)
  | _ -> assert false

let mux (e:exp) (e1:tritype_exp) e2 = match e1, e2 with
  | Exp e1, Exp e2 ->
     Exp { e1 with si_desc = ECall (relocalize e.si_loc "mux", [], [e; e1; e2])}
  | StateExp e1, StateExp e2 ->
     StateExp { e1 with s_desc = ESMux (e, e1, e2) }
  | _ -> assert false

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

(* let constructor_tbl : (UIDConstructor.t, static_int_exp) Hashtbl.t =
 *   Hashtbl.create 16
 *
 * let index c = Hashtbl.find constructor_tbl c.id_uid
 *
 * (\* create bus of width #patterns and fill tbl *\)
 * let enum_to_bus loc e =
 *   let n = List.length e.enum_constructors_names in
 *   let id = UIDIdent.get () in
 *   let name = { id_loc = loc;
 *                id_desc = (e.enum_name.id_desc ^ "bus" ^ (UIDIdent.to_string id));
 *                id_uid  = id } in
 *   let bus = size (EVar name) loc (TNDim [Size (SInt n)]) in
 *   let _, index =
 *     List.fold_left
 *       (fun (i, index) c -> i+1, ConstructEnv.add c.id_uid (slice bus i) index)
 *       (0, ConstructEnv.empty) e.enum_constructors_names
 *   in
 *   bus, index
 *
 * let rec exp (_e:exp) = assert false
 *
 * let rec decl env (d:decl) = match d.desc with
 *   | Dmatch (_e, m) ->
 *      let _, index = enum_to_bus m.m_loc m.m_state_type in
 *
 *      let merge c (env: exp M.t) (acc: exp M.t) =
 *        M.fold (fun lv v acc ->
 *            let e = match M.find_opt lv acc with
 *              | None -> v
 *              | Some e' -> mux (ConstructEnv.find c index) v e' in
 *            M.add lv e acc) env acc
 *      in
 *
 *      (\* recursive calls on handlers *\)
 *      let map : exp M.t ConstructEnv.t =
 *        ConstructEnv.map
 *          (fun h ->
 *            List.fold_left
 *              (fun acc d -> union (decl env d) acc) M.empty h.m_body)
 *          m.m_handlers
 *      in
 *      ConstructEnv.fold merge map M.empty
 *
 *   | Deq ({ b_desc = LValDrop; _ }, _) -> env
 *   | Deq ({ b_desc = LValId id; _ }, e) ->
 *      M.add id (match e with
 *                | Exp exp -> exp
 *                | StateExp st -> fst @@ enum_to_bus st.s_loc st.s_type
 *                | StateTransitionExp _ -> assert false) env
 *   | Deq ({ b_desc = LValTuple _lvs; _}, _e) -> assert false
 *   | Dif (_c, _b1, _b2) -> assert false (\* TODO *\)
 *
 *   (\* can't occur *\)
 *   | Dreset (_, _) -> assert false
 *   | Dlocaleq (_, _) -> assert false
 *   | Dautomaton _ -> assert false
 *
 * let env2list env =
 *   M.fold (fun id (e:exp) lst ->
 *       let ty =  BNetlist (e.si_size) in
 *       let lv = tritype (LValId id) id.id_loc ty in
 *       (relocalize e.si_loc @@ Deq (lv, Exp e)) :: lst) env []
 *
 * let node (n:node) =
 *   let b = List.map (decl M.empty) n.node_body in
 *   let b = fmap env2list b in
 *   { n with node_body = b } *)

(** enable
    must be done __after__ removing state expressions *)

let bit_type = TNDim [Size (SInt 1)]

let new_en_var _ =
  let uid = UIDIdent.get () in
  let id = { id_uid = uid; id_loc = Location.no_location;
             id_desc = "en" ^ (UIDIdent.to_string uid )} in
  id, size (EVar id) Location.no_location bit_type

let rec en_exp en (e:tritype_exp) = match e with
  | Exp e -> Exp (en_exp' en e)
  | StateExp se -> StateExp (en_sexp en se)
  | StateTransitionExp _ -> assert false

and en_exp_desc en (e:exp_desc) = match e with
  | EConst _ -> e
  | EVar _ -> e
  | EReg e -> EReg (en_exp' en e)
  | EMem (st1, st2, es) -> EMem (st1, st2, List.map (en_exp' en) es)
  | ECall ({ desc = "and"; _ }, _, _)
    | ECall ({ desc = "not"; _ }, _, _)
    | ECall ({ desc = "xor"; _ }, _, _)
    | ECall ({ desc = "or"; _ }, _, _)
    | ECall ({ desc = "concat"; _ }, _, _)
    | ECall ({ desc = "slice_one"; _ }, _, _)
    | ECall ({ desc = "slice_from"; _ }, _, _)
    | ECall ({ desc = "slice_to"; _ }, _, _)
    | ECall ({ desc = "slice_fromto"; _ }, _, _)
    | ECall ({ desc = "slice_all"; _ }, _, _) -> e
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
  | Deq (lv, e) ->
     let tmp_lv, tmp_var = gen_lv "tmp" e in
     [relocalize d.loc @@ Deq (tmp_lv, en_exp en e);
      relocalize d.loc @@ Deq (lv, (mux en tmp_var (reg tmp_var)))]
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
  { n with node_inputs; node_body = fmap (en_decl en) n.node_body }

(** [Matcher.program p] compiles match from a automaton-reset-free ast *)
let program (p:program) =
  (* ConstructEnv.iter (fun _ e ->
   *     List.iteri (fun i c ->
   *         let si = no_localize (SInt i) in
   *         Hashtbl.replace constructor_tbl c.id_uid si)
   *       e.enum_constructors_names) p.p_enums; *)
  { p with p_nodes = FunEnv.map en_node p.p_nodes }

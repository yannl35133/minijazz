open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let fmap f lst = List.flatten @@ List.map f lst

module M = Map.Make(struct type t = ident
                           let compare i1 i2 =
                             UIDIdent.compare i1.id_uid i2.id_uid
                    end)

let union = M.union (fun _ _ _ -> assert false)

(* one bit encoding of enum *)
let build f lst = List.fold_left f ConstructEnv.empty lst

let mux (e:exp) e1 e2 =
  { e1 with si_desc = ECall (relocalize e.si_loc "mux", [], [e; e1; e2])}

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

let constructor_tbl : (UIDConstructor.t, static_int_exp) Hashtbl.t =
  Hashtbl.create 16

let index c = Hashtbl.find constructor_tbl c.id_uid

(* create bus of width #patterns and fill tbl *)
let enum_to_bus loc e =
  let n = List.length e.enum_constructors_names in
  let id = UIDIdent.get () in
  let name = { id_loc = loc;
               id_desc = (e.enum_name.id_desc ^ "bus" ^ (UIDIdent.to_string id));
               id_uid  = id } in
  let bus = size (EVar name) loc (TNDim [Size (SInt n)]) in
  let _, index =
    List.fold_left
      (fun (i, index) c -> i+1, ConstructEnv.add c.id_uid (slice bus i) index)
      (0, ConstructEnv.empty) e.enum_constructors_names
  in
  bus, index

let rec exp (_e:exp) = assert false

let rec decl env (d:decl) = match d.desc with
  | Dmatch (_e, m) ->
     let _, index = enum_to_bus m.m_loc m.m_state_type in

     let merge c (env: exp M.t) (acc: exp M.t) =
       M.fold (fun lv v acc ->
           let e = match M.find_opt lv acc with
             | None -> v
             | Some e' -> mux (ConstructEnv.find c index) v e' in
           M.add lv e acc) env acc
     in

     (* recursive calls on handlers *)
     let map : exp M.t ConstructEnv.t =
       ConstructEnv.map
         (fun h ->
           List.fold_left
             (fun acc d -> union (decl env d) acc) M.empty h.m_body)
         m.m_handlers
     in
     ConstructEnv.fold merge map M.empty

  | Deq ({ b_desc = LValDrop; _ }, _) -> env
  | Deq ({ b_desc = LValId id; _ }, e) ->
     M.add id (match e with
               | Exp exp -> exp
               | StateExp st -> fst @@ enum_to_bus st.s_loc st.s_type
               | StateTransitionExp _ -> assert false) env
  | Deq ({ b_desc = LValTuple _lvs; _}, _e) -> assert false
  | Dif (_c, _b1, _b2) -> assert false (* TODO *)

  (* can't occur *)
  | Dreset (_, _) -> assert false
  | Dlocaleq (_, _) -> assert false
  | Dautomaton _ -> assert false

let env2list env =
  M.fold (fun id (e:exp) lst ->
      let ty =  BNetlist (e.si_size) in
      let lv = tritype (LValId id) id.id_loc ty in
      (relocalize e.si_loc @@ Deq (lv, Exp e)) :: lst) env []

let node (n:node) =
  let b = List.map (decl M.empty) n.node_body in
  let b = fmap env2list b in
  { n with node_body = b }

(** [Matcher.program p] compiles match from a automaton-reset-free ast *)
let program (p:program) =
  ConstructEnv.iter (fun _ e ->
      List.iteri (fun i c ->
          let si = no_localize (SInt i) in
          Hashtbl.replace constructor_tbl c.id_uid si)
        e.enum_constructors_names) p.p_enums;
  { p with p_nodes = FunEnv.map node p.p_nodes }

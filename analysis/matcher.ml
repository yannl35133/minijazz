open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let fmap f lst = List.flatten @@ List.map f lst

module M = Map.Make(struct type t = ident
                           let compare i1 i2 =
                             UIDIdent.compare i1.id_uid i2.id_uid
                    end)

let never = assert false

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

let rec decl env (d:decl) = match d.desc with
  | Dmatch (_e, m) ->
     (* create bus of width #patterns *)
     let n = List.length m.m_state_type.enum_constructors_names in
     let id = UIDIdent.get () in
     let name = { id_loc = m.m_loc;
                  id_desc = ("match" ^ (UIDIdent.to_string id));
                  id_uid  = id } in
     let code = size (EVar name) m.m_loc (TNDim [Size (SInt n)]) in

     (* map all constructor to its slice index of code *)
     let _, index =
       List.fold_left (fun (i, index) c -> i+1, ConstructEnv.add c i index)
         (0, ConstructEnv.empty)
         (List.map (fun c -> c.id_uid) m.m_state_type.enum_constructors_names)
     in

     let merge c (env: exp M.t) (acc: exp M.t) =
       M.fold (fun lv v acc ->
           let i = ConstructEnv.find c index in
           let cond = eand (slice code i) one  in
           let e = mux cond v (M.find lv acc) in
           M.add lv e acc) env acc
     in

     (* recursive calls on handlers *)
     let map : exp M.t ConstructEnv.t =
       ConstructEnv.map
         (fun h ->
           List.fold_left
             (fun env acc -> M.merge never env acc) M.empty
           @@ List.map (decl env) h.m_body)
       m.m_handlers
     in
     ConstructEnv.fold merge map M.empty

  | Deq ({ b_desc = LValDrop; _ }, _) -> env
  | Deq ({ b_desc = LValId id; _ }, e) ->
     M.add id (match e with
               | Exp exp -> exp
               | StateExp _ -> assert false
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
      Deq (lv, Exp e) :: lst) env []

let node (n:node) =
  let b = List.map (decl M.empty) n.node_body in
  let b = fmap env2list b in
  { n with node_body = b }

(** [Matcher.program p] compiles match from a automaton-reset-free ast *)
let program (p:program) = { p with p_nodes = FunEnv.map node p.p_nodes }

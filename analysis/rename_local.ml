open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* rename local variable in a unique way
   also rename every occurence in expressions *)

  let prefix_rename p id = { id with id_desc = p ^ id.id_desc }

  let rec rename_local_exp env (e:exp) =
  let si_desc = match e.si_desc with
    | EConst _ -> e.si_desc
    | EVar id -> (try EVar (Env.find id.id_uid env) with Not_found -> e.si_desc)
    | EReg e -> EReg (rename_local_exp env e)
    | ECall (fname, ps, args) ->
        ECall (fname, ps, List.map (rename_local_exp env) args)
    | EMem (a, b, args) ->
        EMem (a, b, List.map (rename_local_exp env) args)
  in
  { e with si_desc }

and rename_local_state_exp env (e:exp state_exp) =
  let s_desc = match e.s_desc with
    | ESConstr _ -> e.s_desc
    | ESVar id -> (try ESVar (Env.find id.id_uid env) with Not_found -> e.s_desc)
    | ESReg e -> ESReg (rename_local_state_exp env e)
    | ESMux (e, e1, e2) -> ESMux (rename_local_exp env e,
                                  rename_local_state_exp env e1,
                                  rename_local_state_exp env e2)
  in
  { e with s_desc }

and rename_lv env (lv:lvalue) = match lv.b_desc with
  | LValDrop -> lv
  | LValId id -> { lv with b_desc = LValId (Env.find id.id_uid env) }
  | LValTuple lvs ->
      { lv with b_desc = LValTuple (List.map (rename_lv env) lvs)}

and rename_local_decl p (env:ident Env.t) (d:decl) =
  let desc = match d.desc with
    | Deq (lv, Exp e) ->
        Deq (lv, Exp (rename_local_exp env e))
    | Dlocaleq (lv, Exp e) ->
        Dlocaleq (rename_lv env lv, Exp (rename_local_exp env e))
    | Deq (lv, StateExp e) ->
        Deq (lv, StateExp (rename_local_state_exp env e))
    | Dlocaleq (lv, StateExp e) ->
        Deq (rename_lv env lv, StateExp (rename_local_state_exp env e))
    | Deq _ -> assert false
    | Dlocaleq _ -> assert false
    | Dreset (e, d) -> Dreset (rename_local_exp env e,
                              List.map (rename_local_decl p env) d)
    | Dmatch (e, m) ->
        let m_handlers =
          ConstructEnv.map
            (fun h ->
              { h with m_body = List.map (rename_local_decl p env) h.m_body })
            m.m_handlers in
        Dmatch (rename_local_state_exp env e, { m with m_handlers })
    | Dif (c, b1, b2) ->
        let b1 = List.map (rename_local_decl p env) b1 in
        let b2 = List.map (rename_local_decl p env) b2 in
        Dif (c, b1, b2)
    | Dautomaton auto ->
        let p = p ^ auto.a_state_type.enum_name.id_desc ^ "_" in
        let (env:ident Env.t) =
          ConstructEnv.fold (fun _ h env ->
              let p = p ^ h.a_state.id_desc ^ "_" in
              List.fold_left (fill_local_env p) env h.a_body)
            auto.a_handlers env in
        let a_handlers =
          ConstructEnv.map (fun h ->
              let p = p ^ h.a_state.id_desc ^ "_" in
              let a_body = List.map (rename_local_decl p env) h.a_body in
              { h with a_body })
            auto.a_handlers in
        Dautomaton { auto with a_handlers }
  in
  { d with desc }

and fill_local_env_lv p env (lv:lvalue) = match lv.b_desc with
  | LValDrop -> env
  | LValId id -> Env.add id.id_uid (prefix_rename p id) env
  | LValTuple lvs -> List.fold_left (fill_local_env_lv p) env lvs

and fill_local_env p env (d:decl) = match d.desc with
  | Dlocaleq (lv, _) -> fill_local_env_lv p env lv
  | Dautomaton _ -> env
  | Dmatch (_, m) ->
      ConstructEnv.fold
        (fun _ h env -> List.fold_left (fill_local_env p) env h.m_body)
        m.m_handlers env
  | Deq (_, _) -> env
  | Dreset (_, d) -> List.fold_left (fill_local_env p) env d
  | Dif (_, b1, b2) ->
      List.fold_left (fill_local_env p)
        (List.fold_left (fill_local_env p) env b2) b1

let rename_node n =
  { n with node_body =
              List.map (rename_local_decl "local_" Env.empty) n.node_body }

let program p =
  { p with p_nodes = FunEnv.map rename_node p.p_nodes }

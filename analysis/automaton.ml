open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* some utilitary functions to write code *)

let one_bit_type = TNDim [Size (SInt 1)]

let var name loc ty = size (EVar name) loc ty

let zero = { si_desc = EConst (VBit false);
             si_loc = Location.no_location;
             si_size = TNDim [Size (SInt 1)]}

let constr (c:state) (e:enum) = state_type (ESConstr c) c.id_loc e

let reg (e:exp state_exp) = { e with s_desc = ESReg e }

let ereg (e:exp) = { e with si_desc = EReg e }

let eor (e1:exp) (e2:exp) =
  { e1 with si_desc = ECall (relocalize e1.si_loc "or", [], [e1; e2])}

let mux (e:exp) e1 e2 =
  { e1 with s_desc = ESMux (e, e1, e2)}

let eeq (v:exp) (e:exp) =
  match v.si_desc with
  | EVar id ->
     let lv = tritype (LValId id) id.id_loc (BNetlist e.si_size)  in
     relocalize id.id_loc @@ Deq (lv, Exp e)
  | _ -> assert false

let eq v (e:exp state_exp) =
  match v.s_desc with
  | ESVar id ->
     let lv = tritype (LValId id) id.id_loc (BState e.s_type)  in
     relocalize id.id_loc @@ Deq (lv, StateExp e)
  | _ -> assert false

let mtch e hdls = relocalize e.s_loc @@ Dmatch (e, hdls)

let prefix p id = { id with id_desc = p ^ id.id_desc }

(** [new_var prefix location ty] introduce a fresh variable *)
let new_var ty p loc =
  let id = UIDIdent.get () in
  let name = { id_loc = loc;
               id_desc = (p ^ (UIDIdent.to_string id));
               id_uid  = id } in
  var name loc ty

(* one bit type variable *)
let new_bvar = new_var one_bit_type
let new_evar name enum : exp state_exp =
  state_type (ESVar name) name.id_loc enum

(** [automaton_reduction p] takes a program and
    transform the ast in order to remove all automaton constructions *)

let fmap f lst = List.flatten @@ List.map f lst

let nx_state_tbl : (UIDIdent.t, exp state_exp) Hashtbl.t = Hashtbl.create 16
let find_nx_st e_uid = Hashtbl.find nx_state_tbl e_uid
let insert_nx_st e_uid exp = Hashtbl.replace nx_state_tbl e_uid exp

let reset_tbl : (UIDConstructor.t, exp) Hashtbl.t = Hashtbl.create 16
let find_rst e_uid = Hashtbl.find reset_tbl e_uid
let insert_rst e_uid exp = Hashtbl.replace reset_tbl e_uid exp

let uid_gen =
  let cnt = ref 0 in
  fun str -> incr cnt; str ^ (string_of_int !cnt)

let rec decl env (d:decl) = match d.desc with
  | Dautomaton a ->

     (* produce list of equations to compute next states from escapes
        /!\ es is ordered from last escape to first
        - es is the list of escapes to process
        - cur is the current enum type
        - nx is the current state expression
        - lst contains remaining equations (if multiple enum types) *)
     let end_esc rstenv lst =
       ConstructEnv.fold (fun c cond lst -> eeq (find_rst c) cond :: lst)
         rstenv lst
     in

     let rec esc_red es (cur, nx, lst, rstenv) = match es with
       | [] -> end_esc rstenv (eq (find_nx_st cur) nx :: lst)
       | (cond, tr) :: es ->
          let reset, nx_st = match tr.st_desc with
            | ESTContinue st -> false, st
            | ESTRestart  st -> true, st
          in

          let rstenv =
            if not reset then rstenv
            else let uid = match nx_st.s_desc with
                   | ESConstr c -> c.id_uid
                   | _ -> assert false in
                 match ConstructEnv.find_opt uid rstenv with
                 | Some a -> ConstructEnv.add uid (eor cond a) rstenv
                 | None   -> ConstructEnv.add uid cond rstenv
          in

          let nx_st_uid = nx_st.s_type.enum_name.id_uid in

          if cur = nx_st_uid
          then let exp = mux cond nx_st nx in
               match es with
               | [] -> end_esc rstenv (eq (find_nx_st nx_st_uid) exp :: lst)
               | es -> esc_red es (cur, exp, lst, rstenv)
          else
            (* if e_cond hold we stay in same cur-state
               otherwise we stick we the update computed so far *)
            let cur_nx_st = find_nx_st cur in
            let exp = mux cond (Env.find cur env) cur_nx_st in
            let lst = eq cur_nx_st exp :: lst in

            let exp = mux cond nx_st (Env.find nx_st_uid env) in
            match es with
            | [] -> end_esc rstenv (eq (find_nx_st nx_st_uid) exp :: lst)
            | es -> esc_red es (nx_st_uid, exp, lst, rstenv)
     in

     let auto_id = uid_gen "auto" in
     let e = a.a_state_type in
     let p = prefix auto_id e.enum_name in

     (* create match handlers *)
     let hdl_red h =
       (* remember in which state we are *)
       let st_var = constr h.a_state a.a_state_type in
       let env' = Env.add e.enum_name.id_uid st_var env in
       let body = fmap (decl env') h.a_body in

       (* for the moment dont handle hard transitions *)

       let escs = (* /!\ dont forget reverse *)
         esc_red (List.rev h.a_strong_transition)
           (* if no condition holds, stay in same state *)
           (e.enum_name.id_uid, constr h.a_state e, [], ConstructEnv.empty) in

       { m_state = h.a_state;
         m_hloc  = h.a_hloc;
         m_body  = body @ escs }
     in


     let nx_st = new_evar (prefix "nx_state" p) e in
     insert_nx_st e.enum_name.id_uid nx_st;

     ConstructEnv.iter (fun c h ->
         let rst_var : exp =
           new_bvar ("rst_state" ^ (UIDConstructor.to_string c)) h.a_hloc
         in
         insert_rst c rst_var)
       a.a_handlers;

     let hdls = ConstructEnv.map hdl_red a.a_handlers in
     let matcher = { m_state_type = e; m_loc = a.a_loc; m_handlers = hdls } in

     (* [match reg(nx_st) with hdls ] *)
     [relocalize a.a_loc @@ Dmatch (reg nx_st, matcher)]

  | Dlocaleq (lv, e) ->
     assert (not (Env.is_empty env));
     let cond =
       let enum_id, fst_st = Env.choose env in
       let fst_st = match fst_st.s_desc with
         | ESConstr st -> find_rst st.id_uid
         | _ -> assert false in
       Env.fold (fun id c cond ->
           if id = enum_id then cond
           else match c.s_desc with
                | ESConstr st -> eor (ereg (find_rst st.id_uid)) cond
                | _ -> assert false)
         env fst_st
     in
     [relocalize d.loc @@ Dreset (cond, [relocalize d.loc @@ Deq (lv, e)])]

  (* fmap reduction on ast *)
  | Dreset (e, ds) ->
     [relocalize d.loc @@ Dreset (e, fmap (decl env) ds)]
  | Dmatch (e, m) ->
     let m_handlers =
       ConstructEnv.map
         (fun h -> { h with m_body = fmap (decl env) h.m_body })
         m.m_handlers in
     [relocalize d.loc @@ Dmatch (e, { m with m_handlers })]
  | Dif (c, d1, d2) ->
     let d1 = fmap (decl env) d1 in
     let d2 = fmap (decl env) d2 in
     [relocalize d.loc @@ Dif (c, d1, d2)]
  | Deq _ -> [d]

(* rename local variable in unique way
   also rename evry occurence in expressions *)

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
       let p = p ^ auto.a_state_type.enum_name.id_desc in
       let (env:ident Env.t) =
         ConstructEnv.fold (fun _ h env ->
             let p = p ^ h.a_state.id_desc in
             List.fold_left (fill_local_env p) env h.a_body)
           auto.a_handlers env in
       let a_handlers =
         ConstructEnv.map (fun h ->
             let p = p ^ h.a_state.id_desc in
             let a_body = List.map (rename_local_decl p env) h.a_body in
             { h with a_body })
           auto.a_handlers in
       Dautomaton { auto with a_handlers }
  in
  { d with desc }

and fill_local_env_lv p env (lv:lvalue) = match lv.b_desc with
  | LValDrop -> env
  | LValId id -> Env.add id.id_uid (prefix p id) env
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
             List.map (rename_local_decl "local" Env.empty) n.node_body }

let rename_program p =
  { p with p_nodes = FunEnv.map rename_node p.p_nodes }

let node n  =
  { n with node_body = fmap (decl Env.empty) n.node_body }

let program (p:program) =
  { p with p_nodes = FunEnv.map node p.p_nodes }

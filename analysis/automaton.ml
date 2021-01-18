open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* some utilitary functions to write code *)

let one_bit_type = TNDim []

let var name loc ty = size (EVar name) loc ty

let zero = { si_desc = EConst (VBit false);
             si_loc = Location.no_location;
             si_size = TNDim []}

let constr (c:state) (e:enum) = state_type (ESConstr c) c.id_loc e

let reg (e:exp state_exp) = { e with s_desc = ESReg e }

let ereg (e:exp) = { e with si_desc = EReg e }

let eor (e1:exp) (e2:exp) =
  { e1 with si_desc = ECall (relocalize e1.si_loc "or", [], [e1; e2])}

(* if e = 1 then e1 else e2 *)
let mux (e:exp) e1 e2 =
  { e1 with s_desc = ESMux (e, e2, e1) }

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

     let e = a.a_state_type in

     (* create match handlers *)
     let hdl_red h =
       (* remember in which state we are *)
       let st_var = constr h.a_state a.a_state_type in
       let env' = Env.add e.enum_name.id_uid st_var env in
       let body = List.concat_map (decl env') h.a_body in

       (* for the moment dont handle hard transitions *)

       let escs = (* /!\ dont forget reverse *)
         esc_red (List.rev h.a_weak_transition)
           (* if no condition holds, stay in same state *)
           (e.enum_name.id_uid, constr h.a_state e, [], ConstructEnv.empty) in

       { m_state = h.a_state;
         m_hloc  = h.a_hloc;
         m_body  = body @ escs }
     in


     let auto_id = uid_gen ("automaton_" ^ !*!(e.enum_name) ^ "_") in
     let state_var = identify a.a_loc auto_id (UIDIdent.get ()) in
     let next_state_var = identify a.a_loc ("next_" ^ auto_id) (UIDIdent.get ()) in
     let st = new_evar state_var e in
     let nx_st = new_evar next_state_var e in
     insert_nx_st e.enum_name.id_uid nx_st;

     ConstructEnv.iter (fun c h ->
         let rst_var : exp =
           new_bvar ("rst_state" ^ (UIDConstructor.to_string c)) h.a_hloc
         in
         insert_rst c rst_var)
       a.a_handlers;

     let hdls = ConstructEnv.map hdl_red a.a_handlers in
     let matcher = { m_state_type = e; m_loc = a.a_loc; m_handlers = hdls } in

     (* [match st (=reg(nx_st)) with hdls ] *)
     let lv = tritype (LValId state_var) !*@state_var (BState e) in
     [
       relocalize a.a_loc @@ Deq (lv, StateExp (reg nx_st));
       relocalize a.a_loc @@ Dmatch (st, matcher)
     ]

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
     [relocalize d.loc @@ Dreset (e, List.concat_map (decl env) ds)]
  | Dmatch (e, m) ->
     let m_handlers =
       ConstructEnv.map
         (fun h -> { h with m_body = List.concat_map (decl env) h.m_body })
         m.m_handlers in
     [relocalize d.loc @@ Dmatch (e, { m with m_handlers })]
  | Dif (c, d1, d2) ->
     let d1 = List.concat_map (decl env) d1 in
     let d2 = List.concat_map (decl env) d2 in
     [relocalize d.loc @@ Dif (c, d1, d2)]
  | Deq _ -> [d]

let node n  =
  { n with node_body = List.concat_map (decl Env.empty) n.node_body }

let program (p:program) =
  { p with p_nodes = FunEnv.map node p.p_nodes }

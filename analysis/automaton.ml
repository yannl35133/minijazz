open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* some utilitary functions to write code *)

let one_bit_type = TNDim [Size (SInt 1)]

let var name loc ty = size (EVar name) loc ty

let constr (c:state) (e:enum) = state_type (EConstr c) c.id_loc e

let reg (e:exp state_exp) = { e with s_desc = ESReg e }

let mux (e:exp) e1 e2 =
  { e1 with s_desc = ESMux (e, e1, e2)}

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

let rec decl env (d:decl) = match d.desc with
  | Dautomaton a ->

     (* produce list of equations to compute next states from escapes
        /!\ es is ordered from last escape to first
        - es is the list of escapes to process
        - cur is the current enum type
        - nx is the current state expression
        - lst contains remaining equations (if multiple enum types) *)
     let rec esc_red es (cur, nx, lst) = match es with
       | [] -> eq (find_nx_st cur) nx :: lst
       | (cond, tr) :: es ->
          (* TODO reset *)
          let _reset, nx_st = match tr.st_desc with
            | EContinue st -> false, st
            | ERestart  st -> true, st
          in

          let nx_st_uid = nx_st.s_type.enum_name.id_uid in

          if cur = nx_st_uid
          then let exp = mux cond nx_st nx in
               match es with
               | [] -> eq (find_nx_st nx_st_uid) exp :: lst
               | es -> esc_red es (cur, exp, lst)
          else
            (* if e_cond hold we stay in same cur-state
               otherwise we stick we the update computed so far *)
            let cur_nx_st = find_nx_st cur in
            let exp = mux cond (Env.find cur env) cur_nx_st in
            let lst = eq cur_nx_st exp :: lst in

            let exp = mux cond nx_st (Env.find nx_st_uid env) in
            match es with
            | [] -> eq (find_nx_st nx_st_uid) exp :: lst
            | es -> esc_red es (nx_st_uid, exp, lst)
     in

     let e = a.a_state_type in
     let p = prefix "auto" e.enum_name in

     (* create match handlers *)
     let hdl_red h =
       (* remember in which state we are *)
       let st_var = constr h.a_state a.a_state_type in
       let env' = Env.add e.enum_name.id_uid st_var env in
       let body = fmap (decl env') h.a_body in

       (* for the moment dont handle hard transitions *)
       assert (h.a_strong_transition = []);

       let escs =
         esc_red (List.rev h.a_weak_transition) (* /!\ dont forget reverse *)
           (* if no condition holds, stay in same state *)
           (e.enum_name.id_uid, constr h.a_state e, []) in

       { m_state = h.a_state;
         m_hloc  = h.a_hloc;
         m_body  = body @ escs }
     in

     let hdls = ConstructEnv.map hdl_red a.a_handlers in
     let matcher = { m_state_type = e; m_loc = a.a_loc; m_handlers = hdls } in

     (* [st = reg(nx_st)] *)
     let st    = new_evar (prefix "cur_state" p) e in
     let nx_st = new_evar (prefix "nx_state" p) e in
     let st_eq = eq st (reg nx_st) in
     [st_eq; relocalize a.a_loc @@ Dmatch (st, matcher)]

  | Dlocaleq (_lv, _e) -> assert false

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

let node n  =
  { n with node_body = fmap (decl Env.empty) n.node_body }

let program (p:program) =
  { p with p_nodes = FunEnv.map node p.p_nodes }

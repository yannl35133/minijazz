open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* some utilitary functions to write code *)

let one_bit_type = TDim [Size (SInt 1)]
let enum_type _enum_name = one_bit_type (* TODO *)

let constr name enum = size (EConstr name) name.loc (enum_type enum)

let var name loc ty = size (EVar name) loc ty

let reg (e:exp) = { e with s_desc = EReg e }

let mux (e:exp) e1 e2 =
  { e1 with s_desc = ECall (relocalize e.s_loc "mux", [], [e; e1; e2])}

let eq v (e:exp) =
  match v.s_desc with
  | EVar id -> relocalize id.loc @@ Deq ({ v with s_desc = LValId id } , e)
  | _ -> assert false

let block lst = Dblock lst

let mtch e hdls = relocalize e.s_loc @@ Dmatch (e, hdls)

let prefix p id = relocalize !@id @@ p ^ !!id

(** [new_var prefix location ty] introduce a fresh variable *)
let new_var ty p loc =
  let id = UniqueId.get () in
  let name = { loc; desc = (p ^ (UniqueId.to_string id)) } in
  var name loc ty

(* one bit type variable *)
let new_bvar = new_var one_bit_type
let new_evar enum = new_var (enum_type enum)

(** [automaton_reduction p] takes a program and
    transform the ast in order to remove all automaton constructions *)

(* associate constructor name with the corresponding state variable name
   returns the _next state_ variable, the one match at next cycle *)
let automaton_tbl : (string, exp) Hashtbl.t = Hashtbl.create 16
let find_nx_st = Hashtbl.find automaton_tbl

(* associate constructor with the corresponding enum type *)
let constructor_tbl : (string, string) Hashtbl.t = Hashtbl.create 16
let find_ty = Hashtbl.find constructor_tbl

let add_enum vars constructors =
  List.iter (fun c -> Hashtbl.replace automaton_tbl c.desc vars) constructors

let rec auto_decl_red_desc env (d:decl) = match d.desc with
  | Dautomaton hdls ->
     (* get nx_state variable and enum type name corresponding to automaton *)
     let some_st = !!(List.hd (List.map (fun h -> h.s_state) hdls)) in
     let nx_st = find_nx_st some_st in
     let enum_ty = find_ty some_st in

     (* produce list of equations to compute next states from escapes
        /!\ es is ordered from last escape to first
        - es is the list of escapes to process
        - cur is the current enum type
        - nx is the current state expression
        - lst contains remaining equations (if multiple enum types) *)
     let rec esc_red es (cur, nx, lst) = match es with
       | [] -> eq (find_nx_st cur) nx :: lst
       | e :: es ->
          let enum = find_ty e.e_nx_state.desc in
          let e_nx_st = constr e.e_nx_state enum in
          if cur = enum
          then let exp = mux e.e_cond e_nx_st nx in
               match es with
               | [] -> eq (find_nx_st enum) exp :: lst
               | es -> esc_red es (cur, exp, lst)
          else
            (* if e_cond hold we stay in same cur-state
               otherwise we stick we the update computed so far *)
            let cur_nx_st = find_nx_st cur in
            let exp = mux e.e_cond (constr (Env.find cur env) enum) cur_nx_st in
            let lst = eq cur_nx_st exp :: lst in

            let exp = mux e.e_cond e_nx_st (constr (Env.find enum env) enum) in
            match es with
            | [] -> eq (find_nx_st enum) exp :: lst
            | es -> esc_red es (enum, exp, lst)
     in

     (* create match handlers *)
     let hdl_red hdl =
       (* each body is wrapped into a reset with its own variable *)
       let reset = new_bvar ("rst"^enum_ty^hdl.s_state.desc)
                     hdl.s_state.loc in

       (* remember in what state we are in *)
       let env' = Env.add enum_ty hdl.s_state env in
       let body = Dreset (auto_decl_red env' hdl.s_body, reset) in
       let body = relocalize hdl.s_body.loc body in

       (* for the moment dont handle hard transitions *)
       assert (hdl.s_unless = []);

       let escs =
         esc_red (List.rev hdl.s_until) (* /!\ dont forget reverse *)
           (* if no condition holds, stay in same state *)
           (enum_ty, constr hdl.s_state enum_ty, []) in

       { m_constr = prefix enum_ty hdl.s_state;
         m_body = relocalize hdl.s_body.loc @@ block (body :: escs) }
     in

     let hdls = List.map hdl_red hdls in

     (* [st = reg(nx_st)] *)
     let st = new_evar enum_ty ("cur_state"^enum_ty) d.loc in
     let st_eq = eq st (reg nx_st) in
     Dblock [st_eq; mtch st hdls]

  (* fmap reduction on ast *)
  | Dblock ds -> Dblock (List.map (auto_decl_red env) ds)
  | Dreset (d, e) -> Dreset (auto_decl_red env d, e)
  | Dmatch (e, hdls) ->
     let hdls =
       List.map
         (fun h -> { h with m_body = auto_decl_red env h.m_body }) hdls in
     Dmatch (e, hdls)
  | Dif (c, d1, d2) ->
     let d1 = { d1 with block = auto_decl_red env d1.block } in
     let d2 = { d2 with block = auto_decl_red env d2.block } in
     Dif (c, d1, d2)
  | (Deq _) as d -> d
  | Dempty as d -> d

and auto_decl_red env d =
  { d with desc = auto_decl_red_desc env d }

(** [produce_enum body] fill automaton_tbl with all required enumerate type
    one for all automaton. Name of enumerate type for automaton has pattern
    `automaton(uid)` and state `s` becomes constructor `automaton(uid)s` *)

let rec produce_enum enums (d:decl) = match d.desc with
  | Dautomaton hdls ->
     let id = UniqueId.get () in
     let name = "automaton" ^ (UniqueId.to_string id) in

     let nx_st = new_evar name name d.loc in
     List.iter (fun h -> Hashtbl.replace automaton_tbl !!(h.s_state) nx_st) hdls;

     let cnames = List.map (fun h ->
                      relocalize h.s_state.loc @@ name ^ h.s_state.desc) hdls in
     List.iter (fun c -> Hashtbl.replace constructor_tbl !!c name) cnames;

     { enum_name = relocalize d.loc name;
       enum_pats = cnames;
       enum_loc  = Location.no_location } :: enums

  (* fmap *)
  | Dempty
  | Deq (_, _) -> enums
  | Dblock ds -> List.fold_left produce_enum enums ds
  | Dreset (d, _) -> produce_enum enums d
  | Dmatch (_, hdls) ->
     List.fold_left (fun enums h-> produce_enum enums h.m_body) enums hdls
  | Dif (_, c1, c2) -> produce_enum (produce_enum enums c1.block) c2.block

let auto_node_reduction node_name n (enums, nodes) =
  let enums = produce_enum enums n.node_body in
  let node_desc = { n with node_body = auto_decl_red Env.empty n.node_body } in
  enums, Env.add node_name node_desc nodes

let automaton_reduction (p:program) =
  Hashtbl.clear automaton_tbl;
  Hashtbl.clear constructor_tbl;
  let p_enums, p_nodes =
    Env.fold auto_node_reduction p.p_nodes (p.p_enums, Env.empty) in
  { p with p_nodes; p_enums }

(** [match_reduction p] takes a program and
    transform the ast in order to remove all match constructions
    here we assume no automaton are left *)
let match_reduction (_p:program) = assert false

(** [reset_reduction p] takes a program and
    transform the ast in order to remove all reset constructions
    here we assume no automaton nor match are left *)
let reset_reduction (_p:program) = assert false

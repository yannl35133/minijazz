open CommonAST
open StaticScopedAST

module StringEnv = Map.Make (struct type t = ident_desc let compare = String.compare end)
module StringSet = Set.Make (struct type t = ident_desc let compare = String.compare end)

exception MissingVariable of (string * Location.location)
exception VariableAlreadyDeclared of (string * Location.location)
exception InputOutput of (string * Location.location)
exception EmptySwitch of Location.location

let static_exp consts_uids ?(params_order=StringEnv.empty) =
  let rec desc : ParserAST.static_exp_desc -> static_exp_desc = function
  | ParserAST.SInt n -> SInt n
  | ParserAST.SBool b -> SBool b
  | ParserAST.SIdent id ->
    if StringEnv.mem !!id params_order then
      SParam (re_identify id (StringEnv.find !!id params_order))
    else if StringEnv.mem !!id consts_uids then
      SConst (re_identify id (StringEnv.find !!id consts_uids))
    else
      raise (Errors.Scope_error (!!id, !@id))
  | ParserAST.SPar e -> desc e.desc
  | ParserAST.SUnOp (sunop, se1)     -> SUnOp (sunop, aux se1)
  | ParserAST.SBinOp (sop, se1, se2) -> SBinOp (sop, aux se1, aux se2)
  | ParserAST.SIf (seb, se1, se2)    -> SIf (aux seb, aux se1, aux se2)
  and aux se = relocalize_fun desc se
  in aux

let static_exp_full (consts_uids, params_order) =
  static_exp consts_uids ~params_order

let optional_static_exp env e = match !!e with
  | SUnknown uid -> relocalize !@e (SUnknown uid)
  | SExp ed ->
      let res = static_exp_full env (relocalize !@e ed) in
      relocalize !@res (SExp !!res)

let slice_param env = function
  | SliceAll ->       SliceAll
  | SliceOne x ->     SliceOne  (optional_static_exp env x)
  | SliceFrom lo ->   SliceFrom (optional_static_exp env lo)
  | SliceTo hi ->     SliceTo   (optional_static_exp env hi)
  | Slice (lo, hi) -> Slice (optional_static_exp env lo, optional_static_exp env hi)

let rec exp_desc (constrs_uids, fun_set, vars_uids, static_env as env) = function
  | ParserAST.EConst c -> EConst c
  | ParserAST.EConstr id ->
      EConstr (re_identify id @@ Misc.option_get ~error:(Errors.Scope_error (!!id, !@id)) @@ StringEnv.find_opt !!id constrs_uids)
  | ParserAST.EVar id ->
      EVar (re_identify id @@ Misc.option_get ~error:(Errors.Scope_error (!!id, !@id)) @@ StringEnv.find_opt !!id vars_uids)
  | ParserAST.EPar e ->
      exp_desc env e.desc
  | ParserAST.ESupOp (id, args) ->
      ESupOp (id, List.map (exp env) args)
  | ParserAST.ESlice (params, e) ->
      ESlice (List.map (slice_param static_env) params, exp env e)
  | ParserAST.EContinue e -> EContinue (exp env e)
  | ParserAST.ERestart e ->  ERestart (exp env e)
  | ParserAST.EReg e ->      EReg (exp env e)
  | ParserAST.ECall (fname, params, args) ->
      if not (StringSet.mem !!fname fun_set) then raise (Errors.Scope_error (!!fname, !@fname));
      let params = List.map (optional_static_exp static_env) params in
      ECall (fname, params, List.map (exp env) args)
  | ParserAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
      let addr_size = optional_static_exp static_env addr_size in
      let word_size = optional_static_exp static_env word_size in
      let args = List.map (exp env) args in
      EMem (mem_kind, (addr_size, word_size, input_file), args)

and exp env e = relocalize_fun (exp_desc env) e

let rec lvalue vars_uids = relocalize_fun @@ function
  | ParserAST.LValTuple l -> LValTuple (List.map (lvalue vars_uids) l)
  | ParserAST.LValDrop ->    LValDrop
  | ParserAST.LValId id ->   LValId (re_identify id (StringEnv.find !!id vars_uids))


let merge_uids_sets : ident Env.t -> ident Env.t -> ident Env.t = Env.union (fun _ a b -> if a <> b then failwith "Non-unique uid" else Some a)

(**
[add_vars_lvalue] adds var/uid couples to [vars_uids].
If [var] is already in [vars_uids], raise [VariableAlreadyDeclared].
If [var] is in [already_declared], use its uid instead of a fresh one
*)
let rec add_vars_lvalue already_declared (uids_set, vars_uids) lvalue = match !!lvalue with
  | ParserAST.LValTuple l -> List.fold_left (add_vars_lvalue already_declared) (uids_set, vars_uids) l
  | ParserAST.LValDrop ->    (uids_set, vars_uids)
  | ParserAST.LValId id ->
      let vars_uid = StringEnv.update !!id
        (function
        | None -> begin match StringEnv.find_opt !!id already_declared with Some uid -> Some uid | None -> Some (UIDIdent.get ()) end
        | Some _ -> raise @@ VariableAlreadyDeclared (!!id, !@id))
        vars_uids
      in
      let uid = StringEnv.find !!id vars_uid in
      Env.add uid (re_identify id uid) uids_set, vars_uid

let rec same_vars_blocks already_declared (uids_set, vars_uids) = function
  | [] ->   (uids_set, vars_uids)
  | [hd] -> add_vars_block already_declared (uids_set, vars_uids) !!hd
  | hd :: tl ->
      let uids_set', reference = add_vars_block already_declared (uids_set, vars_uids) !!hd in
      let new_already_declared = StringEnv.union (fun _ a b -> if a <> b then failwith "Error in add_vars" else Some a) already_declared reference in
      (* The duplication detection happens before the "already_declared" detection, so no problem there *)
      let others = List.map (relocalize_fun (fun b -> snd @@ add_vars_block new_already_declared (uids_set, vars_uids) b)) tl in
      let problem = List.find_opt (fun map -> not @@ StringEnv.equal (=) !!map reference) others in
      match problem with
      | None -> uids_set', reference
      | Some pb ->
        match
          StringEnv.choose_opt (StringEnv.filter (fun el _ -> not @@ StringEnv.mem el reference) !!pb),
          StringEnv.choose_opt (StringEnv.filter (fun el _ -> not @@ StringEnv.mem el !!pb) reference)
        with
        | Some (el, _), _ -> raise (MissingVariable (el, !@hd))
        | _, Some (el, _) -> raise (MissingVariable (el, !@pb))
        | None, None -> failwith "Problem in symmetric difference of maps"


and add_vars_decl already_declared vars_envs decl = match !!decl with
  | ParserAST.Deq (lv, _) ->                add_vars_lvalue already_declared vars_envs lv
  | ParserAST.Dlocaleq (_, _) ->            vars_envs (* local eqs will be considered in the second pass, they are not global *)
  | ParserAST.Dreset (_, block) ->          add_vars_block already_declared vars_envs block
  | ParserAST.Dif (_, block1, block2) ->    same_vars_blocks already_declared vars_envs [block1; block2]
  | ParserAST.Dautomaton { a_handlers; _ } ->
      let blocks = List.map (fun (handler: ParserAST.automaton_handler) -> relocalize handler.a_hloc handler.a_body) a_handlers in
      same_vars_blocks already_declared vars_envs blocks
  | ParserAST.Dmatch (_, { m_handlers; _ }) ->
      let blocks = List.map (fun (handler: ParserAST.match_handler) -> relocalize handler.m_hloc handler.m_body) m_handlers in
      same_vars_blocks already_declared vars_envs blocks

and add_vars_block already_declared vars_envs = List.fold_left (fun map decl -> add_vars_decl already_declared map decl) vars_envs

let rec match_handler (constrs_uids, _, _, _, _, _ as env) ParserAST.{ m_state; m_hloc; m_body } =
  let m_state =
    if StringEnv.mem !!m_state constrs_uids then
      re_identify m_state (StringEnv.find !!m_state constrs_uids)
    else
      raise (Errors.Scope_error (!!m_state, !@m_state))
  in
  let uids_set, m_body = block env m_body in
  uids_set, { m_state; m_hloc; m_body }


and matcher (_, enum_constrs, _, _, _, _ as env) ParserAST.{ m_handlers; m_loc } =
  let uids_sets, handlers = List.split @@ List.map (match_handler env) m_handlers in
  let one_handler = match handlers with hd :: _ -> hd | [] -> raise (EmptySwitch m_loc) in
  let enum_type = Misc.option_get ~error:(Failure "enum_constrs") @@ ConstructEnv.find_opt !**(one_handler.m_state) enum_constrs in
  let enum_types = List.map (fun { m_state; m_hloc; _ } -> Misc.option_get ~error:(Failure "enum_constrs") @@ ConstructEnv.find_opt !**m_state enum_constrs, m_hloc) handlers in
  try
    let pb, loc = List.find (fun (ti, _) -> !**(ti.enum_name) <> !**(enum_type.enum_name)) enum_types in
    raise (Errors.WrongType (!*!(pb.enum_name), !*!(enum_type.enum_name), loc))
  with Not_found -> ();
  let m_handlers = List.fold_left (fun env handler -> ConstructEnv.add !**(handler.m_state) handler env) ConstructEnv.empty handlers in
  let uids_set = List.fold_left merge_uids_sets Env.empty uids_sets in
  uids_set, { m_state_type = enum_type; m_loc; m_handlers }

and automaton_handler (constrs_uids, enum_constrs, const_uids, fun_set, params_order, vars_uids)
  ParserAST.{ a_state; a_hloc; a_body; a_weak_transition; a_strong_transition } =
  let uids_set, with_local_vars =
    List.fold_left
      (fun vars_uids decl -> match !!decl with ParserAST.Dlocaleq (lv, _) -> add_vars_lvalue StringEnv.empty vars_uids lv | _ -> vars_uids)
      vars_uids a_body
  in
  let exp_env = constrs_uids, fun_set, with_local_vars, (const_uids, params_order) in
  let uids_sets, a_body = List.split @@ List.map (decl (constrs_uids, enum_constrs, const_uids, fun_set, params_order, (uids_set, with_local_vars))) a_body in
  let a_state =
    if StringEnv.mem !!a_state constrs_uids then
      re_identify a_state (StringEnv.find !!a_state constrs_uids)
    else
      raise (Errors.Scope_error (!!a_state, !@a_state))
  in
  let a_weak_transition = List.map (fun (e1, e2) -> exp exp_env e1, exp exp_env e2) a_weak_transition in
  let a_strong_transition = List.map (fun (e1, e2) -> exp exp_env e1, exp exp_env e2) a_strong_transition in
  let uids_set = List.fold_left merge_uids_sets uids_set uids_sets in
  uids_set, { a_state; a_hloc; a_body; a_weak_transition; a_strong_transition }

and automaton (_, enum_constrs, _, _, _, _ as env) ParserAST.{ a_handlers; a_loc } =
  let uids_sets, handlers = List.split @@ List.map (automaton_handler env) a_handlers in
  let fst_handler = match handlers with hd :: _ -> hd | [] -> raise (EmptySwitch a_loc) in
  let enum_type = Misc.option_get ~error:(Failure "enum_constrs") @@ ConstructEnv.find_opt !**(fst_handler.a_state) enum_constrs in
  let enum_types = List.map (fun { a_state; a_hloc; _ } -> Misc.option_get ~error:(Failure "enum_constrs") @@ ConstructEnv.find_opt !**a_state enum_constrs, a_hloc) handlers in
  try
    let pb, loc = List.find (fun (ti, _) -> !**(ti.enum_name) <> !**(enum_type.enum_name)) enum_types in
    raise (Errors.WrongType (!*!(pb.enum_name), !*!(enum_type.enum_name), loc))
  with Not_found -> ();
  let a_handlers = List.fold_left (fun env handler -> ConstructEnv.add !**(handler.a_state) handler env) ConstructEnv.empty handlers in
  let uids_set = List.fold_left merge_uids_sets Env.empty uids_sets in
  uids_set, { a_state_type = enum_type; a_fst_state = fst_handler.a_state; a_loc; a_handlers }

and decl (constrs_uids, _, const_uids, fun_set, params_order, (uids_set, vars_uids) as env) : ParserAST.decl -> ident Env.t * decl =
  let static_env = const_uids, params_order in
  let exp_env = constrs_uids, fun_set, vars_uids, static_env in
  (fun f a -> let (b, c) = f !!a in b, relocalize !@a c) @@ function
  | ParserAST.Deq (lv, e) ->                uids_set, Deq (lvalue vars_uids lv, exp exp_env e)
  | ParserAST.Dlocaleq (lv, e) ->           uids_set, Dlocaleq (lvalue vars_uids lv, exp exp_env e)
  | ParserAST.Dreset (condition, eqs) ->
      let uids_set, eqs = block env eqs in
      uids_set, Dreset (exp exp_env condition, eqs)
  | ParserAST.Dif (condition, block1, block2) ->
      let uids_set1, block1 = block env !!block1 in
      let uids_set2, block2 = block env !!block2 in
      merge_uids_sets uids_set1 uids_set2, Dif (static_exp_full static_env condition, block1, block2)
  | ParserAST.Dmatch (switch, matcher0) ->
      let uids_set, matcher0 = matcher env matcher0 in
      uids_set, Dmatch (exp exp_env switch, matcher0)
  | ParserAST.Dautomaton (auto) ->
      let uids_set, auto = automaton env auto in
      uids_set, Dautomaton auto

and block (constrs_uids, enum_constrs, const_uids, fun_set, params_order, vars_uids) lst =
  let uids_set, with_local_vars =
    List.fold_left
      (fun vars_uids decl -> match !!decl with ParserAST.Dlocaleq (lv, _) -> add_vars_lvalue StringEnv.empty vars_uids lv | _ -> vars_uids)
      vars_uids lst
  in
  let uids_sets, b = List.split @@ List.map (decl (constrs_uids, enum_constrs, const_uids, fun_set, params_order, (uids_set, with_local_vars))) lst in
  List.fold_left merge_uids_sets uids_set uids_sets, b

let body (constrs_uids, enum_constrs, const_uids, fun_set, params_order, input_vars, output_vars) lst =
  let merge_idents_uid key a b =
    match a, b with
    | Some _, Some _ -> raise (InputOutput (key, !@lst)) (* If we could unite them beforehand, this wouldn't be excluded *)
    | Some a, None -> Some a
    | None, Some b -> Some b
    | None, None -> None (* What ? *)
  in
  let input_vars = input_vars
    |> List.map (fun { ti_name; _ } -> (!*!ti_name, !**ti_name))
    |> List.to_seq |> StringEnv.of_seq
  in
  let output_vars = output_vars
    |> List.map (fun { ti_name; _ } -> (!*!ti_name, !**ti_name))
    |> List.to_seq |> StringEnv.of_seq
  in
  let uids_set, vars_uids = add_vars_block (StringEnv.merge merge_idents_uid input_vars output_vars) (Env.empty, StringEnv.empty) !!lst in
  try
    let pb, _ = StringEnv.choose @@ StringEnv.filter (fun el _ -> not @@ StringEnv.mem el vars_uids) output_vars in
    raise (MissingVariable (pb, !@lst))
  with Not_found -> ();
  block (constrs_uids, enum_constrs, const_uids, fun_set, params_order, (uids_set, vars_uids)) !!lst

let starput (enum_env, static_env) ParserAST.{ ti_name; ti_type; ti_loc } =
  let rec fun_netlist_type: ParserAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_netlist_type l)
    | TNDim l -> TNDim (List.map (optional_static_exp static_env) l)
  in
  let fun_global_type: ParserAST.global_type -> size global_type  = function
    | BNetlist ti -> BNetlist (fun_netlist_type ti)
    | BState s -> BState (
        match StringEnv.find_opt !!s enum_env with
        | Some s -> s
        | None -> raise (Errors.Scope_error (!!s, !@s)))
    | BStateTransition s -> BStateTransition (
        match StringEnv.find_opt !!s enum_env with
        | Some s -> s
        | None -> raise (Errors.Scope_error (!!s, !@s)))
  in
  { ti_name = re_identify ti_name (UIDIdent.get ()); ti_loc; ti_type = relocalize_fun fun_global_type ti_type }


let node (enum_env, enum_constrs, constrs_uids, consts_uids, fun_set)
  ParserAST.{ node_inline; node_name; node_inputs; node_outputs; node_params; node_body; node_probes = _; node_loc } : node =
  let node_params = List.mapi (fun i ParserAST.{ sti_name; sti_type; sti_loc } -> { sti_name = re_identify sti_name i; sti_type; sti_loc }) node_params in
  let params_order = List.fold_left (fun env { sti_name; _ } -> StringEnv.add !*!sti_name !**sti_name env) StringEnv.empty node_params in

  let node_inputs =  List.map (starput (enum_env, (consts_uids, params_order))) node_inputs in
  let node_outputs = List.map (starput (enum_env, (consts_uids, params_order))) node_outputs in

  let node_variables, node_body = body (constrs_uids, enum_constrs, consts_uids, fun_set, params_order, node_inputs, node_outputs) node_body in
  {
    node_inline;
    node_name;
    node_params;
    node_inputs;
    node_outputs;
    node_body;
    node_variables;
    (* node_probes; *)
    node_loc
  }

let const (consts_uids, consts_env) ParserAST.{ const_left; const_right; const_loc } =
  let uid = UIDIdent.get () in
  (StringEnv.add !!const_left uid consts_uids,
  Env.add uid { const_name = re_identify const_left uid; const_decl = static_exp consts_uids const_right; const_loc } consts_env),
  uid

let enum (enum_env, enum_constrs, constrs_uids) ParserAST.{ enum_name; enum_constructors; enum_loc } =
  let uid = UIDIdent.get () in
  let constructors = List.map (fun name -> re_identify name (UIDConstructor.get ())) enum_constructors in

  let enum = {
    enum_name = re_identify enum_name uid;
    enum_constructors_names = constructors;
    enum_constructors = List.fold_left (fun constrs_set constr -> ConstructSet.add !**constr constrs_set) ConstructSet.empty constructors;
    enum_loc
  }
  in
  (StringEnv.add !!enum_name enum enum_env,
  List.fold_left (fun enum_constrs constr -> ConstructEnv.add !**constr enum enum_constrs) enum_constrs constructors,
  List.fold_left (fun constrs_uids constr -> StringEnv.add !*!constr !**constr constrs_uids) constrs_uids constructors)


let program ParserAST.{ p_enums; p_consts; p_nodes } : program =
  let (enum_env, enum_constrs, constrs_uids) = List.fold_left enum (StringEnv.empty, ConstructEnv.empty, StringEnv.empty) p_enums in
  let (consts_uids, p_consts), p_consts_order = List.fold_left_map const (StringEnv.empty, Env.empty) p_consts in
  let fun_set = List.fold_left (fun set ParserAST.{ node_name; _ } -> StringSet.add !!node_name set) StringSet.empty p_nodes in
  let p_nodes = List.fold_left (
    fun env (ParserAST.{ node_name; _ } as node0) ->
      FunEnv.add !!node_name (node (enum_env, enum_constrs, constrs_uids, consts_uids, fun_set) node0) env
    ) FunEnv.empty p_nodes
  in
  { p_enums = enum_constrs; p_consts; p_consts_order; p_nodes }

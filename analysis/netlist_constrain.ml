open CommonAST
open StaticTypedPartialAST
open NetlistDimensionedAST
open NetlistConstrainedAST

let rec other_context fname loc ctxt = function
  | TProd l -> TProd (List.map (other_context fname loc ctxt) l)
  | TNDim l -> TNDim (List.map (fun p -> PSOtherContext (fname, loc, ctxt, p)) l)

let rec eq_to_constraints c1 c2 : constraints = match c1, c2 with
  | TProd l1, TProd l2 -> List.flatten @@ List.rev_map2 eq_to_constraints l1 l2
  | TNDim l1, TNDim l2 -> List.combine (List.init (List.length l1) (fun _ -> no_localize (SBool true))) @@ List.combine l1 l2
  | TNDim _,  TProd _
  | TProd _,  TNDim _ ->   failwith "Misdimensioned value"

let global_eq_to_constraints (c1: global_presize) c2 = match c1, c2 with
  | BNetlist t1, BNetlist t2 -> eq_to_constraints t1 t2
  | BState s1, BState s2 -> if s1 <> s2 then failwith "Mistype in state" else []
  | BStateTransition s1, BStateTransition s2 -> if s1 <> s2 then failwith "Mistype in state transition" else []
  | _ -> failwith "Mix between states and netlists"

let tritype_of_exp = function
  | Exp e -> BNetlist !&&e
  | StateExp e -> BState e.s_type
  | StateTransitionExp e -> BStateTransition e.st_type


let fun_env_find fun_env id =
  let reloc a = relocalize !@id a in
  let regexp_slice = Str.regexp {|slice\(\(_\(all\|one\|to\|fromto\|from\)\)+\)|} in
  let regexp_supop = Str.regexp {|\(or\|and\|xor\|nand\|nor\|not\|mux\|concat\|add_dim\)_\([0-9]+\)|} in
  if FunEnv.mem !!id fun_env then
    FunEnv.find !!id fun_env
  else if Str.string_match regexp_slice !!id 0 then begin
    let args = List.tl @@ String.split_on_char '_' @@ Str.matched_group 1 !!id in
    let dim = List.length args in
    let params_dim i =
      reloc (SIParam (identify !@id ("dim_" ^ string_of_int i) i))
    in
    let dims_in = List.init dim (fun i -> PSConst (params_dim i)) in
    let add se1 se2 = reloc (SIBinOp (SAdd, se1, se2)) in
    let add_one se = add se (reloc (SInt 1)) in
    let minus se1 se2 = reloc (SIBinOp (SMinus, se1, se2)) in
    let minus_one se = minus se (reloc (SInt 1)) in
    let param loc name nb = reloc (SIParam (identify loc name nb)) in
    let rec aux idim_in idim_out iparam = function
      | "all"  :: tl ->   PSConst (params_dim idim_out) :: aux (idim_in+1) (idim_out+1) iparam tl
      | "one"  :: tl ->                                    aux idim_in (idim_out+1) (iparam+1) tl
      | "from" :: tl ->   PSConst (add_one (minus (minus_one (params_dim idim_out)) (param !@id ("from_" ^ string_of_int idim_in) iparam))) :: aux (idim_in+1) (idim_out+1) (iparam+1) tl
      | "to"   :: tl ->   PSConst (add_one (param !@id ("to_" ^ string_of_int idim_in) iparam)) :: aux (idim_in+1) (idim_out+1) (iparam+1) tl
      | "fromto" :: tl -> PSConst (add_one (minus (param !@id ("fromto_to_" ^ string_of_int idim_in) (iparam+1)) (param !@id ("fromto_from_" ^ string_of_int idim_in) iparam))) :: aux (idim_in+1) (idim_out+1) (iparam+2) tl
      | [] -> []
      | _ -> failwith "Miscounted arguments in slice"
    in
    let dims_out = TNDim (aux 0 0 dim args) in
    [TNDim dims_in], dims_out
  end else if Str.string_match regexp_supop !!id 0 then begin
    let op = Str.matched_group 1 !!id in
    let dim = int_of_string @@ Str.matched_group 2 !!id in
    let dims_in_list = List.init dim (fun i -> PSConst (reloc (SIParam (identify !@id ("dim_" ^ string_of_int i) i)))) in
    let dims_in = TNDim dims_in_list in
    if op = "concat" then begin
      if dim < 1 then failwith "Undefined function in presizing";
      let tail_in = List.init (dim-1) (fun i -> PSConst (reloc (SIParam (identify !@id ("dim_" ^ string_of_int (i+1)) (i+2))))) in
      let param0, param1 = reloc (SIParam (identify !@id "dim_0_arg_1" 0)), reloc (SIParam (identify !@id "dim_0_arg_2" 1)) in
      [TNDim (PSConst param0 :: tail_in); TNDim (PSConst param1 :: tail_in)],
      TNDim (PSConst (reloc (SIBinOp (SAdd, param0, param1))) :: tail_in)
    end else if op = "not" then
      [dims_in], dims_in
    else if op = "mux" then
      [TNDim []; dims_in; dims_in], dims_in
    else if op = "add_dim" then
      [dims_in], TNDim (PSConst (reloc (SInt 1)) :: dims_in_list)
    else
      [dims_in; dims_in], dims_in
  end else
    failwith "Undefined function in presizing"

let rom_ram_size mem_kind =
  let addr_size = PSConst (relocalize !@mem_kind (SIParam (identify !@mem_kind "addr_size" 0))) in
  let word_size = PSConst (relocalize !@mem_kind (SIParam (identify !@mem_kind "word_size" 1))) in
  match !!mem_kind with
  | MRom ->
      "rom", [TNDim [addr_size]], TNDim [word_size]
  | MRam ->
      "ram", [TNDim [addr_size]; TNDim []; TNDim [addr_size]; TNDim [word_size]], TNDim [word_size]

let size_value loc v =
  let rec assert_size sizes value = match sizes, value with
    | n :: tl, VNDim l -> if n <> List.length l then raise (Errors.NonConstantSize loc); List.iter (assert_size tl) l
    | [],      VBit _ ->  ()
    | _ :: _,  VBit _ ->  raise (Errors.NonConstantDimension loc)
    | [],      VNDim _ -> raise (Errors.NonConstantDimension loc)
  in
  let rec search_size depth = function
    | VNDim (hd :: tl) -> let r = search_size depth hd in List.iter (assert_size r) tl; (List.length tl + 1) :: r
    | VNDim [] -> if depth > 0 then raise (Errors.ZeroWideBusMulti (depth, loc)) else [0]
    | VBit _ -> []
  in
  TNDim (List.map (fun n -> PSConst (relocalize loc (SInt n))) (search_size 0 v))


let rec exp (fun_env, var_env as env) constraints e = match !%!e with
  | NetlistDimensionedAST.EConst c ->
      let size = size_value !%@e c in
      constraints, presize (EConst c) !%@e size
  | NetlistDimensionedAST.EVar id -> begin
      match Env.find_opt !**id var_env with
        | None -> failwith "Undefined variable in presizing"
        | Some BNetlist size -> constraints, presize (EVar id) !%@e size
        | Some BState _ -> failwith "Unxpected state"
        | Some BStateTransition _ -> failwith "Unxpected state transition"
      end
  | NetlistDimensionedAST.EReg e1 ->
      let constraints, e1 = exp env constraints e1 in
      let size = match !&&e1 with
        | TProd _ -> failwith "UnexpectedProd in sizing"
        | TNDim l -> TNDim l
      in
      constraints, presize (EReg e1) !%@e size
  | NetlistDimensionedAST.ECall (fname, params, args) ->
      let dims_in, dims_out = fun_env_find fun_env fname in
      let dims_in = List.map (other_context !!fname !%@e params) dims_in in
      let dims_out = other_context !!fname !%@e params dims_out in
      let constraints, dim_args = List.fold_left_map (exp env) constraints args in
      let new_constraints = List.concat @@ List.rev_map2 eq_to_constraints dims_in @@ List.map (!&&) dim_args in
      new_constraints @ constraints, presize (ECall (fname, params, dim_args)) !%@e dims_out
  | NetlistDimensionedAST.EMem (mem_kind, (addr_size, word_size, _ as params), args) ->
      let fname, dims_in, dims_out = rom_ram_size mem_kind in
      let re_params = [relocalize !@addr_size @@ SOIntExp !!addr_size; relocalize !@word_size @@ SOIntExp !!word_size] in
      let dims_in = List.map (other_context fname !%@e re_params) dims_in in
      let dims_out = other_context fname !%@e re_params dims_out in
      let constraints, dim_args = List.fold_left_map (exp env) constraints args in
      let new_constraints = List.concat @@ List.rev_map2 eq_to_constraints dims_in @@ List.map (!&&) dim_args in
      new_constraints @ constraints, presize (EMem (mem_kind, params, dim_args)) !%@e dims_out


let rec state_exp fun_env constraints e = match e.s_desc with
  | ESConstr c -> constraints, re_state_type e @@ ESConstr c
  | ESMux (a, b, c) ->
      let constraints, a' = exp fun_env constraints a in
      let constraints, b' = state_exp fun_env constraints b in
      let constraints, c' = state_exp fun_env constraints c in
      constraints, re_state_type e @@ ESMux (a', b', c')
  | ESVar id -> constraints, re_state_type e @@ ESVar id
  | ESReg a ->
      let constraints, a' = state_exp fun_env constraints a in
      constraints, re_state_type e @@ ESReg a'

let state_transition_exp fun_env constraints e = match e.st_desc with
    | ESTContinue a ->
        let constraints, a' = state_exp fun_env constraints a in
        constraints, re_state_transition_type e @@ ESTContinue a'
    | ESTRestart a ->
      let constraints, a' = state_exp fun_env constraints a in
      constraints, re_state_transition_type e @@ ESTRestart a'

let tritype_exp env constraints : NetlistDimensionedAST.tritype_exp -> constraints * NetlistConstrainedAST.tritype_exp = function
  | Exp e ->
      let constraints, e' = exp env constraints e in
      constraints, Exp e'
  | StateExp e ->
      let constraints, e' = state_exp env constraints e in
      constraints, StateExp e'
  | StateTransitionExp e ->
      let constraints, e' = state_transition_exp env constraints e in
      constraints, StateTransitionExp e'

let rec dim_to_blank_presize name = function
  | NDim n ->  TNDim (List.init n (fun idim -> PSVar (name, idim, UIDUnknownStatic.get ())))
  | NProd l -> TProd (List.map (dim_to_blank_presize name) l)

let global_to_blank_presize name = function
  | BNetlist ti -> BNetlist (dim_to_blank_presize name ti)
  | BState s -> BState s
  | BStateTransition s -> BStateTransition s

let rec lvalue0 var_env lval = match !?!lval with
  | LValDrop ->
      tritype LValDrop !?@lval (global_to_blank_presize (identify !?@lval "_" (UIDIdent.get ())) !??lval)
  | LValId id ->
      let size = Misc.option_get ~error:(Failure "Undefined variable in presizing") @@ Env.find_opt !**id var_env in
      tritype (LValId id) !?@lval size
  | LValTuple l ->
      let size_l = List.map (lvalue0 var_env) l in
      let extract dim = match !??dim with
      | BNetlist n -> n
      | _ -> failwith "Not implemented mixed state / netlist tuples"
      in
      let size = List.map extract size_l in
      tritype (LValTuple size_l) !?@lval (BNetlist (TProd size))

let rec size_to_presize name = function
  | TNDim l -> TNDim (List.mapi (fun i { desc; loc } ->
      match desc with
      | SUnknown uid -> PSVar (name, i, uid)
      | SExp e -> PSConst (relocalize loc e)) l)
  | TProd l -> TProd (List.map (size_to_presize name) l)
and global_size_to_presize name = function
  | BNetlist ti -> BNetlist (size_to_presize name ti)
  | BState s -> BState s
  | BStateTransition s -> BStateTransition s

let rec assert_dim_to_presize loc = function
  | TNDim l, NDim n when List.length l = n -> ()
  | TProd l, NProd l' -> List.iter (assert_dim_to_presize loc) (List.combine l l')
  | TNDim l, NDim n ->   raise (Errors.WrongDimension (List.length l, n, loc))
  | TProd _, NDim _ ->   raise (Errors.WrongType ("variable", "tuple", loc))
  | TNDim _, NProd _ ->  raise (Errors.WrongType ("tuple", "variable", loc))

let assert_global_to_presize loc = function
  | BNetlist ti1, BNetlist ti2 -> assert_dim_to_presize loc (ti1, ti2)
  | BState s1, BState s2 when s1 = s2 -> ()
  | BStateTransition s1, BStateTransition s2 when s1 = s2 -> ()
  | _ -> failwith "No state type hints implemented"

let rec assert_lvalue0 var_env constraints ti lval =
  assert_global_to_presize !?@lval (ti, !??lval);
  match !?!lval with
  | LValDrop ->
      let ps = global_size_to_presize (identify !?@lval "_" (UIDIdent.get ())) ti in
      constraints, tritype LValDrop !?@lval ps
  | LValId id ->
      let ps = global_size_to_presize id ti in
      let size = Misc.option_get ~error:(Failure "Undefined variable in presizing") @@ Env.find_opt !**id var_env in
      let new_constraints = global_eq_to_constraints ps size in
      new_constraints @ constraints, tritype (LValId id) !?@lval ps
  | LValTuple l ->
      let l' = match ti with BNetlist TProd l -> List.map (fun t -> BNetlist t) l | _ -> assert false in
      let constraints, size_l = Misc.fold_left_map2 (assert_lvalue0 var_env) constraints l' l in
      let extract dim = match !??dim with
      | BNetlist n -> n
      | _ -> failwith "Not implemented mixed state / netlist tuples"
      in
      let size = List.map extract size_l in
      constraints, tritype (LValTuple size_l) !?@lval (BNetlist (TProd size))

let lvalue var_env constraints { lval; lval_type } =
  let constraints, lval' = match !!lval_type with
  | Some ti -> assert_lvalue0 var_env constraints ti lval
  | None -> constraints, lvalue0 var_env lval
  in
  constraints, { lval = lval'; lval_loc = !@lval_type }


let add_guard g c = match !!g with
  | SBool true -> c
  | _ -> relocalize !@c (SBBinOp (SAnd, g, c))

let rec decl (_, var_env as env) constraints (d: NetlistDimensionedAST.decl) = match !!d with
  | Deq (lval, e) ->
      let constraints, e' = tritype_exp env constraints e in
      let constraints, lval' = lvalue var_env constraints lval in
      let new_constraints = global_eq_to_constraints !??(lval'.lval) (tritype_of_exp e') in
      new_constraints @ constraints, relocalize !@d @@ Deq (lval', e')
  | Dlocaleq (lval, e) ->
      let constraints, e' = tritype_exp env constraints e in
      let constraints, lval' = lvalue var_env constraints lval in
      let new_constraints = global_eq_to_constraints !??(lval'.lval) (tritype_of_exp e') in
      new_constraints @ constraints, relocalize !@d @@ Dlocaleq (lval', e')
  | Dif (c, b1, b2) ->
      let new_constraints, b1' = block env [] b1 in
      let new_constraints = List.map (fun (g, e) -> add_guard g c, e) new_constraints in
      let new_constraints, b2' = block env new_constraints b2 in
      new_constraints @ constraints, relocalize !@d @@ Dif (c, b1', b2')
  | Dreset (e, b) ->
      let constraints, e' = exp env constraints e in
      let constraints, b' = block env constraints b in
      constraints, relocalize !@d @@ Dreset (e', b')
  | Dmatch (e, m) ->
      let constraints, m' = matcher env constraints m in
      let constraints, e' = state_exp env constraints e in
      constraints, relocalize !@d @@ Dmatch (e', m')
  | Dautomaton a ->
      let constraints, a' = automaton env constraints a in
      constraints, relocalize !@d @@ Dautomaton a'

and match_handler env constraints ({ m_body; _} as handler) =
  let constraints, m_body = block env constraints m_body in
  constraints, { handler with m_body }

and matcher env constraints ({ m_handlers; _} as matcher) =
  let constraints, m_handlers = constructenv_map_fold1 (match_handler env) constraints m_handlers in
  constraints, { matcher with m_handlers }

and transition env =
  List.fold_left_map (fun constraints (e1, e2) ->
    let constraints, e1' = exp env constraints e1 in
    let constraints, e2' = state_transition_exp env constraints e2 in
    constraints, (e1', e2'))

and automaton_handler env constraints ({ a_body; a_weak_transition; a_strong_transition; _ } as handler) =
  let constraints, a_body = block env constraints a_body in
  let constraints, a_weak_transition = transition env constraints a_weak_transition in
  let constraints, a_strong_transition = transition env constraints a_strong_transition in
  constraints, { handler with a_body; a_weak_transition; a_strong_transition}

and automaton fun_env constraints ({ a_handlers; _} as auto) =
  let constraints, a_handlers = constructenv_map_fold2 (automaton_handler fun_env) constraints a_handlers in
  constraints, { auto with a_handlers }

and constructenv_map_fold1 handler_one constraints s_handlers = (* Typing would not le me use the same function twice *)
  ConstructEnv.fold
    (fun uid handler (constraints, re_handlers') ->
      let constraints, handler' = handler_one constraints handler in
      constraints, ConstructEnv.add uid handler' re_handlers'
    ) s_handlers (constraints, ConstructEnv.empty)

and constructenv_map_fold2 handler_one constraints s_handlers =
  ConstructEnv.fold
    (fun uid handler (constraints, re_handlers') ->
      let constraints, handler' = handler_one constraints handler in
      constraints, ConstructEnv.add uid handler' re_handlers'
    ) s_handlers (constraints, ConstructEnv.empty)

and block env = List.fold_left_map (decl env)


let rec presize_of_netlist_type name = function
  | TProd l -> (TProd (List.map (presize_of_netlist_type name) l))
  | TNDim l -> (TNDim (List.mapi
  (fun i opt_static_exp -> match !!opt_static_exp with
    | SUnknown uid -> PSVar (name, i, uid)
    | SExp se -> PSConst (relocalize !@opt_static_exp se)
    ) l))

let global_of_netlist_type name = function
  | BNetlist ti -> BNetlist (presize_of_netlist_type name ti)
  | BState s -> BState s
  | BStateTransition s -> BStateTransition s

let true_global_of_netlist_type name = function
  | BNetlist ti -> (presize_of_netlist_type name ti)
  | _ -> failwith "Not implemented state arguments in functions"

let starput var_env0 { ti_name; ti_type; ti_loc } =
  Env.add !**ti_name (global_of_netlist_type ti_name !!ti_type) var_env0,
  { ti_name; ti_loc; ti_type = relocalize !@ti_type @@ global_of_netlist_type ti_name !!ti_type }

let node fun_env ({ node_inputs; node_outputs; node_body; node_variables; _ } as node) : constraints * node =

  let var_env0 = Env.empty in
  let var_env0, node_inputs = List.fold_left_map starput var_env0 node_inputs in
  let var_env0, node_outputs = List.fold_left_map starput var_env0 node_outputs in

  let get_presize typed_id =
    match Env.find_opt !** !?!typed_id var_env0 with
    | None -> global_to_blank_presize !?!typed_id !??typed_id
    | Some s -> s
  in
  let node_variables0 = Env.map get_presize node_variables in
  let constraints, node_body = block (fun_env, node_variables0) [] node_body in
  let node_variables = Env.mapi (fun key ti -> let id = Env.find key node_variables in tritype !?!id !?@id ti) node_variables0 in

  List.rev constraints,
  { node with
    node_inputs;
    node_outputs;
    node_body;
    node_variables
  }


let fun_env { node_inputs; node_outputs; _ } =
  List.map (fun { ti_name; ti_type; _ } -> true_global_of_netlist_type ti_name !!ti_type) node_inputs,
  match List.map (fun { ti_name; ti_type; _ } -> true_global_of_netlist_type ti_name !!ti_type) node_outputs with
  | [out] -> out
  | l -> TProd l

let program ({ p_nodes; _ } as program) : program =
  try
    let fun_env = FunEnv.map fun_env p_nodes in

    let constraints = ref [] in
    let f nod =
      let c, r = node fun_env nod in
      constraints := c @ !constraints;
      r
    in
    let p_nodes = FunEnv.map f p_nodes in
    { program with
      p_nodes
    }, !constraints
  with Errors.WrongType (found, expected, loc) ->
    Format.eprintf "%aType Error: This expression is a %s but a %s was expected@."
      Location.print_location loc found expected;
    raise Errors.ErrorDetected

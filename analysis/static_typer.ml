open CommonAST
open StaticTypedPartialAST
open StaticTypedAST

module IntEnv = Map.Make (Int)

let rec static_int_exp consts_env ?(params_env=IntEnv.empty) se =
  let fi = static_int_exp  consts_env ~params_env in
  let fb = static_bool_exp consts_env ~params_env in
  let static_int_unop sunop se1 = match sunop with
    | ParserAST.SNeg -> SIUnOp (SNeg, fi se1)
    | ParserAST.SNot -> raise Errors.TmpError
  in
  let static_int_binop sbinop se1 se2 = match sbinop with
    | ParserAST.SAdd ->   SIBinOp (SAdd,   fi se1, fi se2)
    | ParserAST.SMinus -> SIBinOp (SMinus, fi se1, fi se2)
    | ParserAST.SMult ->  SIBinOp (SMult,  fi se1, fi se2)
    | ParserAST.SDiv ->   SIBinOp (SDiv,   fi se1, fi se2)
    | ParserAST.SPower -> SIBinOp (SPower, fi se1, fi se2)
    | SEq | SNeq | SLt | SLeq | SGt | SGeq | SOr | SAnd -> raise Errors.TmpError
  in

  try match !!se with
    | StaticScopedAST.SInt n ->
        relocalize !@se (SInt n)
    | StaticScopedAST.SBool _ ->
        raise Errors.TmpError
    | StaticScopedAST.SConst id -> begin
        match Env.find_opt !**id consts_env with
          | Some TInt -> relocalize !@se (SIConst id)
          | Some TBool -> raise Errors.TmpError
          | None -> failwith "Unscoped static constant"
        end
    | StaticScopedAST.SParam id -> begin
        match IntEnv.find_opt !**id params_env with
          | Some TInt -> relocalize !@se (SIParam id)
          | Some TBool -> raise Errors.TmpError
          | None -> failwith "Unscoped static parameter"
        end
    | StaticScopedAST.SUnOp (sunop, se1) ->
        relocalize !@se (static_int_unop sunop se1)
    | StaticScopedAST.SBinOp (sop, se1, se2) ->
        relocalize !@se (static_int_binop sop se1 se2)
    | StaticScopedAST.SIf (seb, se1, se2) ->
        relocalize !@se (SIIf (fb seb, fi se1, fi se2))
  with Errors.TmpError -> raise @@ Errors.WrongType ("bool", "int", !@se)


and static_bool_exp consts_env ?(params_env=IntEnv.empty) se =
  let fi = static_int_exp  consts_env ~params_env in
  let fb = static_bool_exp consts_env ~params_env in
  let static_bool_unop sunop se1 = match sunop with
    | ParserAST.SNot -> SBUnOp (SNot, fb se1)
    | ParserAST.SNeg -> raise Errors.TmpError
  in
  let static_bool_binop sbinop se1 se2 = match sbinop with
    | ParserAST.SEq ->  SBBinIntOp (SEq,  fi se1, fi se2)
    | ParserAST.SNeq -> SBBinIntOp (SNeq, fi se1, fi se2)
    | ParserAST.SLt ->  SBBinIntOp (SLt,  fi se1, fi se2)
    | ParserAST.SLeq -> SBBinIntOp (SLeq, fi se1, fi se2)
    | ParserAST.SGt ->  SBBinIntOp (SGt,  fi se1, fi se2)
    | ParserAST.SGeq -> SBBinIntOp (SGeq, fi se1, fi se2)
    | ParserAST.SOr ->  SBBinOp    (SOr,  fb se1, fb se2)
    | ParserAST.SAnd -> SBBinOp    (SAnd, fb se1, fb se2)
    | SAdd | SMinus | SMult | SDiv | SPower -> raise Errors.TmpError
  in

  try
    match !!se with
      | StaticScopedAST.SInt _ ->
          raise Errors.TmpError
      | StaticScopedAST.SBool b ->
          relocalize !@se (SBool b)
      | StaticScopedAST.SConst id -> begin
          match Env.find_opt !**id consts_env with
            | Some TInt -> raise Errors.TmpError
            | Some TBool -> relocalize !@se (SBConst id)
            | None -> failwith "Unscoped static constant"
          end
      | StaticScopedAST.SParam id -> begin
        match IntEnv.find_opt !**id params_env with
          | Some TInt -> raise Errors.TmpError
          | Some TBool -> relocalize !@se (SBParam id)
          | None -> failwith "Unscoped static parameter"
        end
      | StaticScopedAST.SUnOp (sunop, se1) ->
          relocalize !@se (static_bool_unop sunop se1)
      | StaticScopedAST.SBinOp (sop, se1, se2) ->
          relocalize !@se (static_bool_binop sop se1 se2)
      | StaticScopedAST.SIf (seb, se1, se2) ->
          relocalize !@se (SBIf (fb seb, fb se1, fb se2))
    with Errors.TmpError -> raise @@ Errors.WrongType ("int", "bool", !@se)

let static_bitype_exp consts_env ?(params_env=IntEnv.empty) se : static_bitype_exp =
  let int_exp = try Ok (static_int_exp consts_env ~params_env se)
    with Errors.WrongType arg -> Error (Errors.WrongType arg)
  in
  let bool_exp = try Ok (static_bool_exp consts_env ~params_env se)
    with Errors.WrongType arg -> Error (Errors.WrongType arg)
  in
  match int_exp, bool_exp with
    | Ok e, Error _ -> relocalize !@e (SIntExp  !!e)
    | Error _, Ok e -> relocalize !@e (SBoolExp !!e)
    | Ok _, Ok _ ->       raise @@ Errors.NoTypes !@se
    | Error _, Error _ -> raise @@ Errors.TwoTypes !@se

let static_int_exp_full (consts_set, params_env) = static_int_exp consts_set ~params_env
let static_bool_exp_full (consts_set, params_env) = static_bool_exp consts_set ~params_env
let static_bitype_exp_full (consts_set, params_env) = static_bitype_exp consts_set ~params_env


let optional_static_unknown_exp static_env e = match !!e with
  | SUnknown uid -> relocalize !@e (SUnknown uid)
  | SExp ed ->
      let res = static_bitype_exp_full static_env (relocalize !@e ed) in
      relocalize !@res (SExp !!res)

let optional_static_int_exp static_env e : optional_static_int_exp = match !!e with
  | SUnknown uid -> relocalize !@e (SUnknown uid)
  | SExp ed ->
      let res = static_int_exp_full static_env (relocalize !@e ed) in
      relocalize !@res (SExp !!res)

let static_params loc types static_env fname params : static_unknown_exp list =
  let typed_params = List.map (optional_static_unknown_exp static_env) params in
  let static_param el ty = match !!el, ty with
    | SExp SIntExp e1,  TInt ->  relocalize !@el (SOIntExp  (SExp e1))
    | SExp SBoolExp e1, TBool -> relocalize !@el (SOBoolExp (SExp e1))
    | SUnknown uid,     TInt ->  relocalize !@el (SOIntExp  (SUnknown uid))
    | SUnknown uid,     TBool -> relocalize !@el (SOBoolExp (SUnknown uid))
    | SExp SIntExp _,   TBool -> raise @@ Errors.WrongTypeParam ("int", "bool", !@el, !!fname, List.map static_type_to_string types)
    | SExp SBoolExp _,  TInt ->  raise @@ Errors.WrongTypeParam ("bool", "int", !@el, !!fname, List.map static_type_to_string types)
  in
  if typed_params = [] then
    List.map (function
      | TInt -> relocalize loc (SOIntExp (SUnknown (UIDUnknownStatic.get ())))
      | TBool -> relocalize loc (SOBoolExp (SUnknown (UIDUnknownStatic.get ())))
      ) types
  else
    List.map2 static_param typed_params types

let slice_param static_env = function
  | SliceAll ->       SliceAll
  | SliceOne x ->     SliceOne  (optional_static_int_exp static_env x)
  | SliceFrom lo ->   SliceFrom (optional_static_int_exp static_env lo)
  | SliceTo hi ->     SliceTo   (optional_static_int_exp static_env hi)
  | Slice (lo, hi) -> Slice     (optional_static_int_exp static_env lo, optional_static_int_exp static_env hi)

let rec exp ((fun_env: fun_env), static_env as env) =
  relocalize_fun @@ function
  | StaticScopedAST.EConstr c -> EConstr c
  | StaticScopedAST.EContinue e -> EContinue (exp env e)
  | StaticScopedAST.ERestart e ->  ERestart (exp env e)
  | StaticScopedAST.EConst c -> EConst c
  | StaticScopedAST.EVar id -> EVar id
  | StaticScopedAST.ESupOp (id, args) ->
      ESupOp (id, List.map (exp env) args)
  | StaticScopedAST.ESlice (params, e) ->
      ESlice (List.map (slice_param static_env) params, exp env e)
  | StaticScopedAST.EReg e ->
      EReg (exp env e)
  | StaticScopedAST.ECall (fname, params, args) ->
      let types = Misc.option_get ~error:(Failure "Unscoped node") @@ FunEnv.find_opt !!fname fun_env in
      let static_typed_params = static_params !@fname types static_env fname params in
      ECall (fname, static_typed_params, List.map (exp env) args)
  | StaticScopedAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
      let addr_size = optional_static_int_exp static_env addr_size in
      let word_size = optional_static_int_exp static_env word_size in
      let args = List.map (exp env) args in
      EMem (mem_kind, (addr_size, word_size, input_file), args)

let rec fun_netlist_type static_env: StaticScopedAST.netlist_type -> 'a = function
  | TProd l -> TProd (List.map (fun_netlist_type static_env) l)
  | TNDim l -> TNDim (List.map (optional_static_int_exp static_env) l)

let fun_global_type static_env: StaticScopedAST.global_type -> global_type  = function
  | BNetlist ti -> BNetlist (fun_netlist_type static_env ti)
  | BState s -> BState s
  | BStateTransition s -> BStateTransition s

let lvalue static_env StaticScopedAST.{ lval; lval_type } =
  { lval; lval_type = relocalize_fun (Option.map (fun_global_type static_env)) lval_type }

let rec match_handler env ({ m_body; _ } as handler) =
  { handler with m_body = List.map (decl env) m_body }

and matcher env ({ m_handlers; _ } as matcher) =
  { matcher with m_handlers = ConstructEnv.map (match_handler env) m_handlers }

and automaton_handler exp_env ({ a_body; a_weak_transition; a_strong_transition; _ } as handler) =
  { handler with
    a_body = List.map (decl exp_env) a_body;
    a_weak_transition = List.map (fun (e1, e2) -> exp exp_env e1, exp exp_env e2) a_weak_transition;
    a_strong_transition = List.map (fun (e1, e2) -> exp exp_env e1, exp exp_env e2) a_strong_transition;
  }

and automaton env ({ a_handlers; _ } as auto) =
  { auto with a_handlers = ConstructEnv.map (automaton_handler env) a_handlers }

and decl (_, static_env as exp_env) = relocalize_fun @@ function
  | StaticScopedAST.Deq (lv, e) ->          Deq (lvalue static_env lv, exp exp_env e)
  | StaticScopedAST.Dlocaleq (lv, e) ->     Dlocaleq (lvalue static_env lv, exp exp_env e)
  | StaticScopedAST.Dreset (c, eqs) ->      Dreset (exp exp_env c, List.map (decl exp_env) eqs)
  | StaticScopedAST.Dif (c, b1, b2) ->      Dif (static_bool_exp_full static_env c, List.map (decl exp_env) b1, List.map (decl exp_env) b2)
  | StaticScopedAST.Dautomaton (auto) ->    Dautomaton (automaton exp_env auto)
  | StaticScopedAST.Dmatch (e, match0) ->   Dmatch (exp exp_env e, matcher exp_env match0)


let starput static_env ({ ti_type; _ } as typed_ident) =
  let rec fun_netlist_type : StaticScopedAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_netlist_type l)
    | TNDim l -> TNDim (List.map (optional_static_int_exp static_env) l)
  in
  let fun_global_type = function
    | BNetlist ti -> BNetlist (fun_netlist_type ti)
    | BState s -> BState s
    | BStateTransition s -> BStateTransition s
  in
  { typed_ident with ti_type = relocalize_fun fun_global_type ti_type }


let params param_list : StaticTypedPartialAST.static_typed_ident list * static_type IntEnv.t =
  let new_params = List.map (
    fun ({ sti_type; _} as sti) ->
      { sti with sti_type = relocalize !@sti_type @@ static_type_of_string sti_type }
    ) param_list
  in
  let param_env = List.fold_left (fun env { sti_name; sti_type; _ } -> IntEnv.add !**sti_name !!sti_type env) IntEnv.empty new_params in
  new_params, param_env

let fun_env { node_params; _ } =
  List.map (fun { sti_type; _ } -> static_type_of_string sti_type) node_params

let node fun_env consts_env ({ node_params; node_inputs; node_outputs; node_body; _ } as node) : node =
  let new_params, params_env = params node_params in
  { node with
    node_params = new_params;
    node_inputs =   List.map (starput (consts_env, params_env)) node_inputs;
    node_outputs =  List.map (starput (consts_env, params_env)) node_outputs;
    node_body =     List.map (decl (fun_env, (consts_env, params_env))) node_body;
  }

let const consts_env ({ const_decl; _ } as const) =
  { const with const_decl = static_bitype_exp consts_env const_decl }

let program ({ p_enums; p_consts; p_consts_order; p_nodes } : StaticScopedAST.program) : program =
  try
    let type_const { const_decl; _ } = match !!const_decl with
      | SIntExp _ -> TInt
      | SBoolExp _ -> TBool
    in
    let consts_env = List.fold_left (
      fun consts_preenv el ->
        Env.add el (type_const @@ const consts_preenv @@ Env.find el p_consts) consts_preenv
      ) Env.empty p_consts_order in
    let fun_env = FunEnv.map fun_env p_nodes in
    {
      p_enums;
      p_consts = Env.map (const consts_env) p_consts;
      p_consts_order;
      p_nodes = FunEnv.map (node fun_env consts_env) p_nodes
    }
      with Errors.WrongType (s1, s2, loc) ->
        Format.eprintf "%aType Error: This expression has type %s but an expression of type %s was expected@."
          Location.print_location loc s1 s2;
        raise Errors.ErrorDetected

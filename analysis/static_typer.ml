(* open CommonAST
 * open StaticTypedPartialAST
 * open StaticTypedAST
 *
 * let rec static_int_exp consts_env ?(params_env=IntEnv.empty) se =
 *   let fi = static_int_exp  consts_env ~params_env in
 *   let fb = static_bool_exp consts_env ~params_env in
 *   let static_int_unop sunop se1 = match sunop with
 *     | ParserAST.SNeg -> SIUnOp (SNeg, fi se1)
 *     | ParserAST.SNot -> raise Errors.TmpError
 *   in
 *   let static_int_binop sbinop se1 se2 = match sbinop with
 *     | ParserAST.SAdd ->   SIBinOp (SAdd,   fi se1, fi se2)
 *     | ParserAST.SMinus -> SIBinOp (SMinus, fi se1, fi se2)
 *     | ParserAST.SMult ->  SIBinOp (SMult,  fi se1, fi se2)
 *     | ParserAST.SDiv ->   SIBinOp (SDiv,   fi se1, fi se2)
 *     | ParserAST.SPower -> SIBinOp (SPower, fi se1, fi se2)
 *     | SEq | SNeq | SLt | SLeq | SGt | SGeq | SOr | SAnd -> raise Errors.TmpError
 *   in
 *
 *   try match !!se with
 *     | StaticScopedAST.SInt n ->
 *         relocalize !@se (SInt n)
 *     | StaticScopedAST.SBool _ ->
 *         raise Errors.TmpError
 *     | StaticScopedAST.SConst id -> begin
 *         match Env.find !!id consts_env with
 *           | TInt -> relocalize !@se (SIConst id)
 *           | TBool -> raise Errors.TmpError
 *         end
 *     | StaticScopedAST.SParam nb -> begin
 *       match IntEnv.find nb params_env with
 *         | TInt -> relocalize !@se (SIParam nb)
 *         | TBool -> raise Errors.TmpError
 *       end
 *     | StaticScopedAST.SUnOp (sunop, se1) ->
 *         relocalize !@se (static_int_unop sunop se1)
 *     | StaticScopedAST.SBinOp (sop, se1, se2) ->
 *         relocalize !@se (static_int_binop sop se1 se2)
 *     | StaticScopedAST.SIf (seb, se1, se2) ->
 *         relocalize !@se (SIIf (fb seb, fi se1, fi se2))
 *   with Errors.TmpError -> raise @@ Errors.WrongType ("bool", "int", !@se)
 *
 *
 * and static_bool_exp consts_env ?(params_env=IntEnv.empty) se =
 *   let fi = static_int_exp  consts_env ~params_env in
 *   let fb = static_bool_exp consts_env ~params_env in
 *   let static_bool_unop sunop se1 = match sunop with
 *     | ParserAST.SNot -> SBUnOp (SNot, fb se1)
 *     | ParserAST.SNeg -> raise Errors.TmpError
 *   in
 *   let static_bool_binop sbinop se1 se2 = match sbinop with
 *     | ParserAST.SEq ->  SBBinIntOp (SEq,  fi se1, fi se2)
 *     | ParserAST.SNeq -> SBBinIntOp (SNeq, fi se1, fi se2)
 *     | ParserAST.SLt ->  SBBinIntOp (SLt,  fi se1, fi se2)
 *     | ParserAST.SLeq -> SBBinIntOp (SLeq, fi se1, fi se2)
 *     | ParserAST.SGt ->  SBBinIntOp (SGt,  fi se1, fi se2)
 *     | ParserAST.SGeq -> SBBinIntOp (SGeq, fi se1, fi se2)
 *     | ParserAST.SOr ->  SBBinOp    (SOr,  fb se1, fb se2)
 *     | ParserAST.SAnd -> SBBinOp    (SAnd, fb se1, fb se2)
 *     | SAdd | SMinus | SMult | SDiv | SPower -> raise Errors.TmpError
 *   in
 *
 *   try
 *     match !!se with
 *       | StaticScopedAST.SInt _ ->
 *           raise Errors.TmpError
 *       | StaticScopedAST.SBool b ->
 *           relocalize !@se (SBool b)
 *       | StaticScopedAST.SConst id -> begin
 *           match Env.find !!id consts_env with
 *             | TInt -> raise Errors.TmpError
 *             | TBool -> relocalize !@se (SBConst id)
 *           end
 *       | StaticScopedAST.SParam nb -> begin
 *         match IntEnv.find nb params_env with
 *           | TInt -> raise Errors.TmpError
 *           | TBool -> relocalize !@se (SBParam nb)
 *         end
 *       | StaticScopedAST.SUnOp (sunop, se1) ->
 *           relocalize !@se (static_bool_unop sunop se1)
 *       | StaticScopedAST.SBinOp (sop, se1, se2) ->
 *           relocalize !@se (static_bool_binop sop se1 se2)
 *       | StaticScopedAST.SIf (seb, se1, se2) ->
 *           relocalize !@se (SBIf (fb seb, fb se1, fb se2))
 *     with Errors.TmpError -> raise @@ Errors.WrongType ("int", "bool", !@se)
 *
 * let static_unknown_exp consts_env ?(params_env=IntEnv.empty) se : static_unknown_exp =
 *   let int_exp = try Ok (static_int_exp consts_env ~params_env se)
 *     with Errors.WrongType arg -> Error (Errors.WrongType arg)
 *   in
 *   let bool_exp = try Ok (static_bool_exp consts_env ~params_env se)
 *     with Errors.WrongType arg -> Error (Errors.WrongType arg)
 *   in
 *   match int_exp, bool_exp with
 *     | Ok e, Error _ -> relocalize !@e (SIntExp (Some !!e))
 *     | Error _, Ok e -> relocalize !@e (SBoolExp (Some !!e))
 *     | Ok _, Ok _ ->       raise @@ Errors.NoTypes !@se
 *     | Error _, Error _ -> raise @@ Errors.TwoTypes !@se
 *
 * let static_int_exp_full (consts_set, params_env) = static_int_exp consts_set ~params_env
 * let static_bool_exp_full (consts_set, params_env) = static_bool_exp consts_set ~params_env
 * let static_unknown_exp_full (consts_set, params_env) = static_unknown_exp consts_set ~params_env
 *
 *
 * let optional_static_unknown_exp env e = match !!e with
 *   | None -> relocalize !@e None
 *   | Some ed ->
 *       let res = static_unknown_exp_full env (relocalize !@e ed) in
 *       relocalize !@res (Some !!res)
 *
 * let optional_static_int_exp env e : optional_static_int_exp = match !!e with
 *   | None -> relocalize !@e None
 *   | Some ed ->
 *       let res = static_int_exp_full env (relocalize !@e ed) in
 *       relocalize !@res (Some !!res)
 *
 * let static_params types env fname params : static_unknown_exp list =
 *   let typed_params = List.map (optional_static_unknown_exp env) params in
 *   let static_param el ty = match !!el, ty with
 *     | Some SIntExp e1,  TInt ->  relocalize !@el (SIntExp e1)
 *     | Some SBoolExp e1, TBool -> relocalize !@el (SBoolExp e1)
 *     | None,             TInt ->  relocalize !@el (SIntExp None)
 *     | None,             TBool -> relocalize !@el (SBoolExp None)
 *     | Some SIntExp _,   TBool -> raise @@ Errors.WrongTypeParam ("int", "bool", !@el, !!fname, List.map static_type_to_string types)
 *     | Some SBoolExp _,  TInt ->  raise @@ Errors.WrongTypeParam ("bool", "int", !@el, !!fname, List.map static_type_to_string types)
 *   in
 *   List.map2 static_param typed_params types
 *
 * let slice_param env = function
 *   | StaticScopedAST.SliceAll ->       SliceAll
 *   | StaticScopedAST.SliceOne x ->     SliceOne  (optional_static_int_exp env x)
 *   | StaticScopedAST.SliceFrom lo ->   SliceFrom (optional_static_int_exp env lo)
 *   | StaticScopedAST.SliceTo hi ->     SliceTo   (optional_static_int_exp env hi)
 *   | StaticScopedAST.Slice (lo, hi) -> Slice     (optional_static_int_exp env lo, optional_static_int_exp env hi)
 *
 * let rec exp_desc ((fun_env: fun_env), env) = function
 *   | StaticScopedAST.EConst c -> EConst c
 *   | StaticScopedAST.EConstr _ -> assert false
 *   | StaticScopedAST.EVar id -> EVar id
 *   | StaticScopedAST.ESupOp (id, args) ->
 *      ESupOp (id, List.map (exp (fun_env, env)) args)
 *   | StaticScopedAST.ESlice (params, e) ->
 *      ESlice (List.map (slice_param env) params, exp (fun_env, env) e)
 *   | StaticScopedAST.EReg e ->
 *      EReg (exp (fun_env, env) e)
 *   | StaticScopedAST.ECall (fname, params, args) ->
 *      let types = Env.find !!fname fun_env in
 *      let static_typed_params = static_params types env fname params in
 *       ECall (fname, static_typed_params, List.map (exp (fun_env, env)) args)
 *   | StaticScopedAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
 *       let addr_size = optional_static_int_exp env addr_size in
 *       let word_size = optional_static_int_exp env word_size in
 *       let args = List.map (exp (fun_env, env)) args in
 *       EMem (mem_kind, (addr_size, word_size, input_file), args)
 *   | StaticScopedAST.ELet _ -> assert false
 *   | StaticScopedAST.EMerge _ -> assert false
 *
 * and exp env e = relocalize !@e @@ exp_desc env !!e
 *
 * and eq_desc env = function
 *   | StaticScopedAST.EQempty -> EQempty
 *   | StaticScopedAST.EQeq (lv, e) -> EQeq (lv, exp env e)
 *   | StaticScopedAST.EQand es -> EQand (List.map (eq env) es)
 *   | StaticScopedAST.EQlet (e1, e2) -> EQlet (eq env e1, eq env e2)
 *   | StaticScopedAST.EQreset (e, ex) -> EQreset (eq env e, exp env ex)
 *   | StaticScopedAST.EQautomaton _ -> assert false
 *   | StaticScopedAST.EQmatch _ -> assert false
 *
 * and eq env eq = relocalize !@eq @@ eq_desc env !!eq
 *
 * let rec body (fun_env, env) e = relocalize_fun (function
 *   | StaticScopedAST.BIf (condition, block1, block2) -> BIf (static_bool_exp_full env condition, body (fun_env, env) block1, body (fun_env, env) block2)
 *   | StaticScopedAST.BEqs eq_l -> BEqs (List.map (eq (fun_env, env)) eq_l)
 *   ) e
 *
 * let starput env = relocalize_fun @@ fun StaticScopedAST.{ name; typed } ->
 *   let rec fun_typed : StaticScopedAST.netlist_type -> 'a = function
 *     | TProd l -> TProd (List.map fun_typed l)
 *     | TNDim l -> TNDim (List.map (optional_static_int_exp env) l)
 *   in
 *   { name; typed = relocalize_fun fun_typed typed }
 *
 *
 * let params param_list : static_typed_ident list * static_type IntEnv.t =
 *   let new_params = List.map
 *     (fun (param: ParserAST.static_typed_ident) ->
 *       relocalize !@param { st_name = !!param.st_name; st_type = static_type_of_string !!param.st_type_name }
 *     ) param_list in
 *   let param_env = Misc.fold_lefti (fun env i el -> IntEnv.add i !! (!!el.st_type) env) IntEnv.empty new_params in
 *   new_params, param_env
 *
 * let fun_env StaticScopedAST.{ node_params; _ } =
 *   List.map (fun (param: ParserAST.static_typed_ident) -> (!!) @@ static_type_of_string !!param.st_type_name) node_params
 *
 * let node fun_env consts_env StaticScopedAST.{ node_name_loc; node_loc; node_params; node_inline; node_inputs; node_outputs; node_body; node_probes } : node =
 *   let new_params, params_env = params node_params in
 *   {
 *     node_params = new_params;
 *     node_inputs =   List.map (starput (consts_env, params_env)) node_inputs;
 *     node_outputs =  List.map (starput (consts_env, params_env)) node_outputs;
 *     node_body =     body (fun_env, (consts_env, params_env)) node_body;
 *     node_name_loc; node_loc; node_inline; node_probes
 *   }
 *
 * let const consts_env StaticScopedAST.{ const_decl; const_ident; const_total } =
 *   {
 *     const_decl = static_unknown_exp consts_env const_decl;
 *     const_ident; const_total
 *   }
 *
 * let program StaticScopedAST.{ p_consts; p_consts_order; p_nodes } : program =
 *   let type_const { const_decl; _ } = match !!const_decl with
 *     | SIntExp _ -> TInt
 *     | SBoolExp _ -> TBool
 *   in
 *   let consts_env = List.fold_left (fun consts_preenv el -> Env.add el (type_const @@ const consts_preenv @@ Env.find el p_consts) consts_preenv) Env.empty p_consts_order in
 *   let fun_env = Env.map fun_env p_nodes in
 *   { p_consts = Env.map (const consts_env) p_consts;
 *     p_consts_order;
 *     p_nodes = Env.map (node fun_env consts_env) p_nodes;
 *   } *)

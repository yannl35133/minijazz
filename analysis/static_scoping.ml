open CommonAST
open StaticScopedAST

let static_exp consts_set ?(params_order=Env.empty) =
  let rec desc : ParserAST.static_exp_desc -> static_exp_desc = function
  | ParserAST.SInt n -> SInt n
  | ParserAST.SBool b -> SBool b
  | ParserAST.SIdent id ->
     if Env.mem !!id params_order then
       SParam (Env.find !!id params_order)
     else if IdentSet.mem !!id consts_set then SConst id
     else raise (Errors.Scope_error (!!id, !@id))
  | ParserAST.SPar e -> desc e.desc
  | ParserAST.SUnOp (sunop, se1)     -> SUnOp (sunop, aux se1)
  | ParserAST.SBinOp (sop, se1, se2) -> SBinOp (sop, aux se1, aux se2)
  | ParserAST.SIf (seb, se1, se2)    -> SIf (aux seb, aux se1, aux se2)
  and aux se : static_exp = relocalize !@se (desc !!se)
  in aux

let static_exp_full (consts_set, params_order) =
  static_exp consts_set ~params_order

let optional_static_exp env e = match !!e with
  | None -> relocalize !@e None
  | Some ed ->
     let res = static_exp_full env (relocalize !@e ed) in
     relocalize !@res (Some !!res)

let slice_param env = function
  | ParserAST.SliceAll ->       SliceAll
  | ParserAST.SliceOne x ->     SliceOne  (optional_static_exp env x)
  | ParserAST.SliceFrom lo ->   SliceFrom (optional_static_exp env lo)
  | ParserAST.SliceTo hi ->     SliceTo   (optional_static_exp env hi)
  | ParserAST.Slice (lo, hi) ->
     Slice (optional_static_exp env lo, optional_static_exp env hi)

let rec exp_desc env = function
  | ParserAST.EConst c -> EConst c
  | ParserAST.EConstr (Estate0 id) -> EConstr (Estate0 id)
  | ParserAST.EConstr (Estaten (id, es)) ->
     EConstr (Estaten (id, List.map (exp env) es))
  | ParserAST.EVar id -> EVar id
  | ParserAST.EPar e -> exp_desc env e.desc
  | ParserAST.ESupOp (id, args) ->
     ESupOp (id, List.map (exp env) args)
  | ParserAST.ESlice (params, e) ->
     ESlice (List.map (slice_param env) params, exp env e)
  | ParserAST.EReg e -> EReg (exp env e)
  | ParserAST.ECall (fname, params, args) ->
     let params = List.map (optional_static_exp env) params in
     ECall (fname, params, List.map (exp env) args)
  | ParserAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
     let addr_size = optional_static_exp env addr_size in
     let word_size = optional_static_exp env word_size in
     let args = List.map (exp env) args in
     EMem (mem_kind, (addr_size, word_size, input_file), args)
  | ELet _ -> assert false
  | EMerge _ -> assert false

and exp env e = relocalize !@e @@ exp_desc env !!e

and eq_desc env = function
  | ParserAST.EQempty -> EQempty
  | ParserAST.EQeq (lv, e) -> EQeq (lv, exp env e)
  | ParserAST.EQand es -> EQand (List.map (eq env) es)
  | ParserAST.EQlet (e1, e2) -> EQlet (eq env e1, eq env e2)
  | ParserAST.EQreset (e, ex) -> EQreset (eq env e, exp env ex)
  | ParserAST.EQautomaton _ -> assert false
  | ParserAST.EQmatch _ -> assert false

and eq env e = relocalize !@e (eq_desc env !!e)

let rec body env e =
  let aux = function
    | ParserAST.BIf (condition, block1, block2) ->
       BIf (static_exp_full env condition, body env block1, body env block2)
    | ParserAST.BEqs eq_l -> BEqs (List.map (eq env) eq_l)
  in
  relocalize_fun aux e

let starput env = relocalize_fun @@ fun ParserAST.{ name; typed } ->
  let rec fun_typed : ParserAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_typed l)
    | TNDim l -> TNDim (List.map (optional_static_exp env) l)
  in
  { name; typed = relocalize_fun fun_typed typed }


let node consts_set (node: ParserAST.node) : node =
  let ParserAST.{ node_name; node_inline; node_inputs; node_outputs; node_params; node_body; node_probes } = !!node in
  let params_order = Misc.fold_lefti (fun env i el -> Env.add !!(!!el.ParserAST.st_name) i env) Env.empty node_params in
  {
    node_name_loc = !@node_name;
    node_loc =      !@node;
    node_inputs =   List.map (starput (consts_set, params_order)) node_inputs;
    node_outputs =  List.map (starput (consts_set, params_order)) node_outputs;
    node_body =     body (consts_set, params_order) node_body;
    node_inline; node_params; node_probes
  }

let const consts_set const =
  let ParserAST.{ const_left; const_right } = !!const in
  {
    const_decl =  static_exp consts_set const_right;
    const_ident = !@const_left;
    const_total = !@const
  }

let program ParserAST.{ p_consts; p_nodes } : program =
  let consts_set = List.fold_left (fun set el -> IdentSet.add !!(!!el.ParserAST.const_left) set) IdentSet.empty p_consts in
  { p_consts = List.fold_left
    (fun env const_ ->
      Env.add !!(!!const_.ParserAST.const_left) (const consts_set const_) env
    ) Env.empty p_consts;
    p_consts_order = List.map (fun el -> !!(!!el.ParserAST.const_left)) p_consts;
    p_nodes = List.fold_left
    (fun env node_ ->
      Env.add !!ParserAST.(!!node_.node_name) (node consts_set node_) env
    ) Env.empty p_nodes;
  }

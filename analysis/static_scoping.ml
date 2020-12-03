open CommonAST
open StaticScopedAST


let static_exp consts_set ?(params_order=Env.empty) =
  let rec f se = match !!se with
    | ParserAST.SInt n ->                 relocalize !@se (SInt n)
    | ParserAST.SBool b ->                relocalize !@se (SBool b)
    | ParserAST.SIdent id ->              relocalize !@se @@
                                            if Env.mem !!id params_order then
                                              SParam (Env.find !!id params_order)
                                            else if IdentSet.mem !!id consts_set then
                                              SConst id
                                            else
                                              raise (Errors.Scope_error (!!id, !@id))
    | ParserAST.SPar e ->                 f e
    | ParserAST.SUnOp (sunop, se1) ->     relocalize !@se (SUnOp (sunop, f se1))
    | ParserAST.SBinOp (sop, se1, se2) -> relocalize !@se (SBinOp (sop, f se1, f se2))
    | ParserAST.SIf (seb, se1, se2) ->    relocalize !@se (SIf (f seb, f se1, f se2))
  in f
let static_exp_full (consts_set, params_order) = static_exp consts_set ~params_order

let optional_static_exp env e = match !!e with
  | None -> relocalize !@e None
  | Some ed ->
      let res = static_exp_full env (relocalize !@e ed) in
      relocalize !@res (Some !!res)

let slice_param env = function
  | ParserAST.SliceAll ->       SliceAll
  | ParserAST.SliceFrom lo ->   SliceFrom (optional_static_exp env lo)
  | ParserAST.SliceTo hi ->     SliceTo   (optional_static_exp env hi)
  | ParserAST.Slice (lo, hi) -> Slice     (optional_static_exp env lo, optional_static_exp env hi)

let rec exp env e = match !!e with
  | ParserAST.EConst c ->             relocalize !@e (EConst c)
  | ParserAST.EVar id ->              relocalize !@e (EVar id)
  | ParserAST.EPar e ->               exp env e
  | ParserAST.ESupOp (id, args) ->    relocalize !@e (ESupOp (id, List.map (exp env) args))
  | ParserAST.ESelect (params, e) ->  relocalize !@e (ESelect (List.map (optional_static_exp env) params, exp env e))
  | ParserAST.ESlice (params, e) ->   relocalize !@e (ESlice (List.map (slice_param env) params, exp env e))
  | ParserAST.EReg e ->               relocalize !@e (EReg (exp env e))
  | ParserAST.ECall (fname, params, args) ->
                                      relocalize !@e (ECall (fname, List.map (optional_static_exp env) params, List.map (exp env) args))
  | ParserAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
                                      relocalize !@e (EMem (mem_kind, (optional_static_exp env addr_size, optional_static_exp env word_size, input_file), List.map (exp env) args))

let eq env = relocalize_fun @@ fun ParserAST.{ eq_left; eq_right } ->
  { eq_left; eq_right = exp env eq_right }


let rec body env e = relocalize_fun (function
  | ParserAST.BIf (condition, block1, block2) -> BIf (static_exp_full env condition, body env block1, body env block2)
  | ParserAST.BEqs eq_l -> BEqs (List.map (eq env) eq_l)
  ) e

let starput env = relocalize_fun @@ fun ParserAST.{ name; typed } ->
  let rec fun_typed : ParserAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_typed l)
    | TBitArray e -> TBitArray (optional_static_exp env e)
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
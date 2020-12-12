open CommonAST
open StaticTypedPartialAST
open NetlistDimensionedAST

exception CannotDimensionYet


type fun_context =
  ProdArg of string * netlist_dimension list (* funname, fun type *)
type error_context =
  | ErSimple
  | ErRev
  | ErFun of fun_context
  | ErOp of string * Location.location (* opname, reference expression *) 

type prod_context =
  | ProdRev
  | ProdOp of string (* opname *)

exception UnexpectedProd of (Location.location * prod_context) (* Obtained product, expected dimension *)
exception ImpossibleProd of (Location.location * prod_context * fun_context option) (* Expected product, obtained expression which returns dimension *)
exception WrongDimension of (netlist_dimension * netlist_dimension * Location.location * error_context)
exception UndefinedReturnVariables of (string * string * Location.location)


let dim_value loc v =
  let rec assert_height depth = function
    | ParserAST.VNDim l -> List.iter (assert_height (depth - 1)) l
    | ParserAST.VBit _ -> if depth <> 0 then raise (Errors.NonConstantDimension loc)
  in
  let rec search_height depth = function
    | ParserAST.VNDim (hd :: tl) -> let r = search_height (succ depth) hd in List.iter (assert_height r) tl; succ r
    | ParserAST.VNDim [] -> raise (Errors.ZeroWideBusMulti (depth, loc))
    | ParserAST.VBit _ -> 0
  in
  NDim (search_height 0 v)

let supop name args dim =
  let funname = match dim with
    | 0 -> !!name
    | n -> !!name ^ "_" ^ string_of_int n
  in
  let params = List.init dim (fun _ -> no_localize (SIntExp None)) in
  ECall (relocalize !@name funname, params, args)

let slice params dim =
  let n = List.length params in
  if dim < n then
    raise Errors.TmpError;
  let params =
    if dim > n then
      params @ List.init (dim - n) (fun _ -> StaticTypedAST.SliceAll)
    else
      params
  in
  let slice_dim_removed = function
    | StaticTypedAST.SliceAll ->       1
    | StaticTypedAST.SliceOne _ ->     0
    | StaticTypedAST.SliceFrom _ ->    1
    | StaticTypedAST.SliceTo _ ->      1
    | StaticTypedAST.Slice _ ->        1
  in
  let slice_name = function
    | StaticTypedAST.SliceAll ->       "all"
    | StaticTypedAST.SliceOne _ ->     "one"
    | StaticTypedAST.SliceFrom _ ->    "from"
    | StaticTypedAST.SliceTo _ ->      "to"
    | StaticTypedAST.Slice _ ->        "fromto"
  in
  let slice_param = function
    | StaticTypedAST.SliceAll ->       []
    | StaticTypedAST.SliceOne x ->     [relocalize !@x  (SIntExp !!x) ]
    | StaticTypedAST.SliceFrom lo ->   [relocalize !@lo (SIntExp !!lo)]
    | StaticTypedAST.SliceTo hi ->     [relocalize !@hi (SIntExp !!hi)]
    | StaticTypedAST.Slice (lo, hi) -> [relocalize !@lo (SIntExp !!lo); relocalize !@hi (SIntExp !!hi)]
  in
  let dims_remaining = List.fold_left (fun acc el -> acc + slice_dim_removed el) 0 params in
  let size = List.init dim (fun _ -> no_localize @@ SIntExp None) (* One argument per input dimension *)
  and name = String.concat "_" @@ List.map slice_name params
  and args = List.concat_map slice_param params in
  NDim dims_remaining, fun e1 -> ECall (no_localize @@ "slice_" ^ name, size @ args, [e1])


let rec exp fun_env dimensioned e = match !!e with
  | StaticTypedAST.EConst c ->
      let dim = dim_value !@e c in
      dimensioned, dimension (EConst c) !@e dim
  | StaticTypedAST.EVar id -> begin
      try
        match Env.find !!id dimensioned with
        | None -> raise CannotDimensionYet
        | Some dim -> dimensioned, dimension (EVar id) !@e dim
      with Not_found -> raise (Errors.Scope_error (!!id, !@id))
      end
  | StaticTypedAST.ESupOp (op, args) ->
      let f d arg =
        try
          let d, res = exp fun_env d arg in
          d, Some res
        with CannotDimensionYet -> d, None
      in
      let dimensioned, test_dim_args = List.fold_left_map f dimensioned args in
      let dim_ex = List.find_map Fun.id test_dim_args in
      let dim_ex = Misc.option_get ~error:CannotDimensionYet dim_ex in
      let dim = match !%%dim_ex with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@dim_ex, ProdOp !!op)
        | NDim n -> n
      in
      let f dimensioned arg =
        try
          assert_exp fun_env (NDim dim) dimensioned arg
        with (* Errors. *)WrongDimension (n1, n2, loc1, ErSimple) -> raise @@ (* Errors. *)WrongDimension (n1, n2, loc1, ErOp (!!op, !%@dim_ex))
      in
      let dimensioned, dim_args = List.fold_left_map f dimensioned args in      
      dimensioned, dimension (supop op dim_args dim) !@e (NDim dim)
  | StaticTypedAST.ESlice (params, e1) ->
      let dimensioned, e1 = exp fun_env dimensioned e1 in
      let dim = match !%%e1 with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@e1, ProdOp "slice")
        | NDim n -> n
      in
      let dim, exp = try slice params dim with Errors.TmpError -> raise @@ Errors.SliceTooMuch (dim, List.length params, !%@e1) in
      dimensioned, dimension (exp e1) !@e dim
  | StaticTypedAST.EReg e1 ->
      let dimensioned, e1 = exp fun_env dimensioned e1 in
      let dim = match !%%e1 with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@e1, ProdOp "reg")
        | NDim n -> NDim n
      in
      dimensioned, dimension (EReg e1) !@e dim
  | StaticTypedAST.ECall (fname, params, args) ->
      let dims_in, dims_out = Misc.option_get ~error:(Errors.Scope_error (!!fname, !@fname)) @@ Env.find_opt !!fname fun_env in
      let dimensioned, dim_args =
        let f dimensioned dim arg =
          try
            assert_exp fun_env dim dimensioned arg
          with
          | (* Errors. *)WrongDimension (n1, n2, loc1, ErSimple) -> raise @@ (* Errors. *)WrongDimension (n1, n2, loc1, ErFun (ProdArg (!!fname, dims_in)))
          | (* Errors. *)ImpossibleProd (loc1, c, None) -> raise @@ (* Errors. *)ImpossibleProd (loc1, c, Some (ProdArg (!!fname, dims_in)))
        in
        try
          Misc.fold_left_map2 f dimensioned dims_in args
        with Not_found -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, List.length dims_in, !!fname)
      in
      dimensioned, dimension (ECall (fname, params, dim_args)) !@e dims_out
  | StaticTypedAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
      let fname = match !!mem_kind with MRom -> "rom" | MRam -> "ram" in
      let dims_in, dims_out = Misc.option_get (Env.find_opt fname fun_env) in
      let dimensioned, dim_args =
        let f dimensioned dim arg =
          try
            assert_exp fun_env dim dimensioned arg
          with
          | (* Errors. *)WrongDimension (n1, n2, loc1, ErSimple) -> raise @@ (* Errors. *)WrongDimension (n1, n2, loc1, ErFun (ProdArg (fname, dims_in)))
          | (* Errors. *)ImpossibleProd (loc1, c, None) -> raise @@ (* Errors. *)ImpossibleProd (loc1, c, Some (ProdArg (fname, dims_in)))
        in
        try
          Misc.fold_left_map2 f dimensioned dims_in args
        with Not_found -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, List.length dims_in, fname)
      in
      dimensioned, dimension (EMem (mem_kind, (addr_size, word_size, input_file), dim_args)) !@e dims_out

and assert_exp fun_env dim dimensioned e =
  try
    let dimensioned, res = exp fun_env dimensioned e in
    if dim <> !%%res then raise @@ (* Errors. *)WrongDimension (!%%res, dim, !@e, ErSimple);
    dimensioned, res
  with CannotDimensionYet -> match !!e with
  | StaticTypedAST.EConst _ -> failwith "Cannot fail to dimension a constant"      
  | StaticTypedAST.EVar id -> begin
      try
        match Env.find !!id dimensioned with
        | Some dim' when dim <> dim' ->
            raise @@ (* Errors. *)WrongDimension (dim', dim, !@e, ErSimple)
        | None ->
            Env.add !!id (Some dim) dimensioned, dimension (EVar id) !@e dim
        | Some dim' ->
            dimensioned, dimension (EVar id) !@e dim'
      with Not_found -> raise (Errors.Scope_error (!!id, !@id))
      end
  | StaticTypedAST.ESupOp (op, args) ->
      let dim_int = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp (!!op), None)
        | NDim n -> n
      in
      let dimensioned, dim_args = List.fold_left_map (assert_exp fun_env dim) dimensioned args in
      dimensioned, dimension (supop op dim_args dim_int) !@e dim
  | StaticTypedAST.ESlice (params, e1) ->
      let dim_int_pre = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp "slice", None)
        | NDim n -> n
      in
      let slice_dim_removed = function
        | StaticTypedAST.SliceAll ->       1
        | StaticTypedAST.SliceOne _ ->     0
        | StaticTypedAST.SliceFrom _ ->    1
        | StaticTypedAST.SliceTo _ ->      1
        | StaticTypedAST.Slice _ ->        1
      in
      let dims_removed = List.fold_left (fun acc el -> acc + slice_dim_removed el) 0 params in
      let dim_int = dim_int_pre + dims_removed in
      let dimensioned, e1 = assert_exp fun_env (NDim dim_int) dimensioned e1 in
      let dim', exp = try slice params dim_int with Errors.TmpError -> failwith "Problem in computations in backwards slice" in
      if dim <> dim' then failwith "Problem in computations in backwards slice";
      dimensioned, dimension (exp e1) !@e dim'
  | StaticTypedAST.EReg e1 ->
      let dim = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp "reg", None)
        | NDim n -> NDim n
      in
      let dimensioned, e1 = assert_exp fun_env dim dimensioned e1 in      
      dimensioned, dimension (EReg e1) !@e !%%e1
  | StaticTypedAST.ECall _
  | StaticTypedAST.EMem _ ->
      raise CannotDimensionYet (* The dimension of the result does not give further info to dimension the arguments *)


let rec lvalue dimensioned lval = match !!lval with
  | ParserAST.LValDrop -> raise CannotDimensionYet
  | ParserAST.LValId id -> begin
      try
        match Env.find !!id dimensioned with
        | None -> raise CannotDimensionYet
        | Some dim -> dimension (LValId id) !@lval dim
      with Not_found -> failwith "Variable not properly added"
      end
  | ParserAST.LValTuple l ->
      let dim_l = List.map (lvalue dimensioned) l in
      let dim = List.map (!%%) dim_l in
      dimension (LValTuple dim_l) !@lval (NProd dim)

let rec assert_lvalue dim dimensioned lval = match !!lval with
  | ParserAST.LValDrop -> dimensioned, dimension LValDrop !@lval dim
  | ParserAST.LValId id -> begin
      try
        match Env.find !!id dimensioned with
        | Some dim' when dim <> dim' ->
            raise @@ (* Errors. *)WrongDimension (dim', dim, !@lval, ErRev)
        | None ->
            Env.add !!id (Some dim) dimensioned, dimension (LValId id) !@lval dim
        | Some dim' ->
            dimensioned, dimension (LValId id) !@lval dim'
      with Not_found -> failwith "Variable not properly added"
      end
  | ParserAST.LValTuple l ->
      let dim_l = match dim with
        | NProd dim_l -> dim_l
        | NDim _ -> raise @@ (* Errors. *)ImpossibleProd (!@lval, ProdRev, None)
      in
      let dimensioned, dimed_l = Misc.fold_left_map2 (fun dimensioned dim lval -> assert_lvalue dim dimensioned lval) dimensioned dim_l l in
      let dim = List.map (!%%) dimed_l in
      dimensioned, dimension (LValTuple dimed_l) !@lval (NProd dim)


let eqs fun_env (name, loc, outputs) dimensioned eq_l =
  let rec add_vars_lvalue vars lvalue = match !!lvalue with
    | ParserAST.LValDrop -> vars
    | ParserAST.LValId id -> IdentSet.add !!id vars
    | ParserAST.LValTuple l -> List.fold_left add_vars_lvalue vars l
  in
  let vars = List.fold_left (fun s eq -> (add_vars_lvalue s !!eq.StaticTypedAST.eq_left)) IdentSet.empty eq_l in
  Option.fold ~some:(fun var -> raise (UndefinedReturnVariables (var, name, loc))) ~none:() @@ IdentSet.choose_opt @@ IdentSet.diff outputs vars;
  let dimensioned = IdentSet.fold (fun el dimed -> if Env.mem el dimed then dimed else Env.add el None dimed) vars dimensioned in

  let try_dimensioning dimensioned StaticTypedAST.{desc = { eq_left; eq_right }; loc} =
    let dimensioned, r2 = (try let dimensioned, r2 = exp fun_env dimensioned eq_right in dimensioned, Some r2 with CannotDimensionYet -> dimensioned, None) in
    dimensioned, ((try Some (lvalue dimensioned eq_left) with CannotDimensionYet -> None), r2, loc)
  in
  
  let rec dimension_eq (dimensioned, dim_eqs) =
    let dimensioned', dim_eqs' = Misc.fold_left_map2
    (fun dimensioned (eq_left0, eq_right0, loc0 as eq0) (StaticTypedAST.{desc = { eq_left; eq_right }; loc = _} as eq) ->
      match eq_left0, eq_right0 with
      | None, None -> try_dimensioning dimensioned eq
      | Some lval, None -> begin
          try let dimed, r = assert_exp fun_env !%%lval dimensioned eq_right in dimed, (eq_left0, Some r, loc0)
          with CannotDimensionYet -> dimensioned, eq0
          end
      | None, Some exp -> begin
          try let dimed, r = assert_lvalue !%%exp dimensioned eq_left in dimed, (Some r, eq_right0, loc0)
          with CannotDimensionYet -> dimensioned, eq0
          end
      | Some _, Some _ -> dimensioned, eq0
    )
    dimensioned dim_eqs eq_l
    in
    if dimensioned <> dimensioned' then
      dimension_eq (dimensioned', dim_eqs')
    else 
      let var = Env.choose_opt @@ Env.filter (fun _ dim -> dim = None) dimensioned' in
      match var with
      | None -> dimensioned', dim_eqs'
      | Some (one, _) ->
          Errors.raise_warning_dimension (Errors.InsufficientAnnotations (name, loc, one));
          dimension_eq (Env.add one (Some (NDim 0)) dimensioned', dim_eqs')
  in
  let dimensioned, dim_eqs = dimension_eq @@ List.fold_left_map try_dimensioning dimensioned eq_l in
  let _dimensioned = Env.map (Misc.option_get ~error:(Failure "There remained undimensioned variables")) dimensioned in 
  let dim_eqs = List.map (fun (eq_left, eq_right, loc) -> match eq_left, eq_right with
    | Some lval, Some exp ->
        if !%%lval <> !%%exp then
          raise @@ (* Errors. *)WrongDimension (!%%exp, !%%lval, !%@exp, ErSimple)
        else
          relocalize loc { eq_left = lval; eq_right = exp }
    | _ -> failwith "We can have all variables dimensioned, but not be able to dimension everything?"
    ) dim_eqs
  in { equations = dim_eqs }



let rec body fun_env (name, outputs as node_info) dimensioned e = relocalize_fun (function
  | StaticTypedAST.BIf (condition, block1, block2) -> BIf (condition, body fun_env node_info dimensioned block1, body fun_env node_info dimensioned block2)
  | StaticTypedAST.BEqs eq_l -> BEqs (eqs fun_env (name, !@e, outputs) dimensioned eq_l)
  ) e

let rec dimension_of_netlist_type = function
  | StaticTypedAST.TProd l -> NProd (List.map dimension_of_netlist_type l)
  | StaticTypedAST.TNDim l -> NDim (List.length l)

let starput dimensioned StaticTypedAST.{desc = { name; typed }; loc } =
  Env.add !!name (Some (dimension_of_netlist_type !!typed)) dimensioned,
  relocalize loc { name; typed; dim = dimension_of_netlist_type !!typed }

let fun_env StaticTypedAST.{ node_inputs; node_outputs; _ } =
  List.map (fun input -> dimension_of_netlist_type !!(!!input.StaticTypedAST.typed) ) node_inputs,
  NProd (List.map (fun input -> dimension_of_netlist_type !!(!!input.StaticTypedAST.typed)) node_outputs)
  

let node fun_env name StaticTypedAST.{ node_name_loc; node_loc; node_params; node_inline; node_inputs; node_outputs; node_body; node_probes } : node =
  let dimensioned = Env.empty in
  let dimensioned, node_inputs  = List.fold_left_map starput dimensioned node_inputs in
  let dimensioned, node_outputs = List.fold_left_map starput dimensioned node_outputs in
  let output_set = List.fold_left (fun s el -> IdentSet.add !!(!!el.name) s) IdentSet.empty node_outputs in
  {
    node_inputs;
    node_outputs;
    node_body =     body fun_env (name, output_set) dimensioned node_body;
    node_name_loc; node_loc; node_inline; node_params; node_probes
  }

let program StaticTypedAST.{ p_consts; p_consts_order; p_nodes } : program =
  let fun_env = Env.map fun_env p_nodes in
  { 
    p_consts; p_consts_order;
    p_nodes = Env.mapi (node fun_env) p_nodes;
  }

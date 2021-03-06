open CommonAST
open StaticTypedPartialAST
open NetlistDimensionedAST

exception CannotDimensionYet of ident option (* Variable that could not be typed, None for a LValueDrop *)
type 'a dimension_option = ('a, ident option) result
type dim_env = global_type option Env.t

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

type option_tritype =
  | OTNetlist of netlist_dimension option
  | OTState of state_type option
  | OTStateTransition of state_type option

let ot_of_t = function
  | BNetlist ti -> OTNetlist (Some ti)
  | BState s -> OTState (Some s)
  | BStateTransition s -> OTStateTransition (Some s)

exception UnexpectedProd of (Location.location * prod_context) (* Obtained product, expected dimension *)
exception ImpossibleProd of (Location.location * prod_context * fun_context option) (* Expected product, obtained expression which returns dimension *)
exception ImpossibleDimension of (netlist_dimension * Location.location)
exception WrongDimension of (netlist_dimension * netlist_dimension * Location.location * error_context)
exception WrongType of (option_tritype * option_tritype * Location.location * error_context)
exception WrongIndication of (option_tritype * option_tritype * Location.location * error_context)
(* exception UnexpectedState of state_type * Location.location *)
(* exception UnexpectedStateTransition of state_type * Location.location *)
exception UndefinedReturnVariables of (string * string * Location.location)

let rec print_netlist_dimension = function
  | NDim n -> Format.dprintf "%d-dim" n
  | NProd l -> Format.dprintf "@[<hv2>%t@]" (Printers.CommonAst.print_list_naked (Format.dprintf " * ") print_netlist_dimension l)

let print_ot = function
  | OTNetlist Some thing -> print_netlist_dimension thing
  | OTNetlist None -> Format.dprintf "netlist"
  | OTState Some s -> Printers.CommonAst.print_enum_type s
  | OTState None -> Format.dprintf "state"
  | OTStateTransition Some s -> Format.dprintf "%t transition" @@ Printers.CommonAst.print_enum_type s
  | OTStateTransition None -> Format.dprintf "state transition"

let rec dimension_of_netlist_type = function
  | TProd l -> (NProd (List.map dimension_of_netlist_type l))
  | TNDim l -> (NDim (List.length l))

let global_of_netlist_type = function
  | BNetlist ti -> BNetlist (dimension_of_netlist_type ti)
  | BState s -> BState s
  | BStateTransition s -> BStateTransition s

let new_unknown_parameter () =
  SOIntExp (SUnknown (UIDUnknownStatic.get ()))

let dim_value loc v =
  let rec assert_height depth = function
    | VNDim l -> List.iter (assert_height (depth - 1)) l
    | VBit _ -> if depth <> 0 then raise (Errors.NonConstantDimension loc)
  in
  let rec search_height depth = function
    | VNDim (hd :: tl) -> let r = search_height (succ depth) hd in List.iter (assert_height r) tl; succ r
    | VNDim [] -> if depth > 0 then raise (Errors.ZeroWideBusMulti (depth, loc)) else 1
    | VBit _ -> 0
  in
  NDim (search_height 0 v)

let supop name args dim =
  let params = List.init dim (fun _ -> relocalize !@name (new_unknown_parameter ())) in
  ECall (relocalize !@name (!!name ^ "_" ^ string_of_int dim), params, args)

let concat name loc (arg1, n1) (arg2, n2) =
  let reloc a = relocalize loc a in
  let funname, dim, arg1, arg2 = match n1, n2 with
    | 0, 0 -> "concat_1", 1,
        dimension (ECall (reloc "add_dim_0", [], [arg1])) !%@arg1 (NDim 1),
        dimension (ECall (reloc "add_dim_0", [], [arg2])) !%@arg2 (NDim 1)
    | n1, n2 when n2 = n1 -> "concat_" ^ string_of_int n1, n1, arg1, arg2
    | n1, n2 when n2 = n1 - 1 -> "concat_" ^ string_of_int n1, n1, arg1,
        dimension (ECall (reloc @@ "add_dim_" ^ string_of_int n2,
                          List.init n2 (fun _ -> reloc (new_unknown_parameter ())), [arg2])) !%@arg2 (NDim (n2 + 1))
    | n1, n2 when n2 = n1 + 1 -> "concat_" ^ string_of_int n2, n2,
        dimension (ECall (reloc @@ "add_dim_" ^ string_of_int n1,
                          List.init n1 (fun _ -> reloc (new_unknown_parameter ())), [arg1])) !%@arg1 (NDim (n1 + 1)),
        arg2
    | _, _ -> failwith "abs (n2 - n1) > 1"
  in
  let params = List.init (dim + 1) (fun _ -> reloc (new_unknown_parameter ())) in
  let exp = ECall (relocalize !@name funname, params, [arg1; arg2]) in
  dimension exp loc (NDim dim)

let slice params loc dim =
  let reloc a = relocalize loc a in
  let n = List.length params in
  if dim < n then
    raise Errors.TmpError;
  let params =
    if dim > n then
      params @ List.init (dim - n) (fun _ -> SliceAll)
    else
      params
  in
  let slice_dim_remaining = function
    | SliceAll ->       1
    | SliceOne _ ->     0
    | SliceFrom _ ->    1
    | SliceTo _ ->      1
    | Slice _ ->        1
  in
  let slice_name = function
    | SliceAll ->       "all"
    | SliceOne _ ->     "one"
    | SliceFrom _ ->    "from"
    | SliceTo _ ->      "to"
    | Slice _ ->        "fromto"
  in
  let slice_param = function
    | SliceAll ->       []
    | SliceOne x ->     [relocalize !@x  (SOIntExp !!x) ]
    | SliceFrom lo ->   [relocalize !@lo (SOIntExp !!lo)]
    | SliceTo hi ->     [relocalize !@hi (SOIntExp !!hi)]
    | Slice (lo, hi) -> [relocalize !@lo (SOIntExp !!lo); relocalize !@hi (SOIntExp !!hi)]
  in
  let dims_remaining = List.fold_left (fun acc el -> acc + slice_dim_remaining el) 0 params in
  let size = List.init dim (fun _ -> reloc (new_unknown_parameter ())) (* One argument per input dimension *)
  and name = String.concat "_" @@ List.map slice_name params
  and args = List.concat_map slice_param params in
  NDim dims_remaining, fun e1 -> ECall (reloc @@ "slice_" ^ name, size @ args, [e1])


let rec exp (fun_env: fun_env) dimensioned (e: StaticTypedAST.exp) = match !!e with
  | EConst c ->
      let dim = dim_value !@e c in
      dimensioned, dimension (EConst c) !@e dim
  | EVar id -> begin
      try
        match Env.find !**id dimensioned with
        | None -> raise (CannotDimensionYet (Some id))
        | Some BNetlist dim -> dimensioned, dimension (EVar id) !@e dim
        | Some (BState _ | BStateTransition _ as ti) -> raise (WrongType (ot_of_t ti, OTNetlist None, !@e, ErSimple))
      with Not_found -> raise (Errors.Scope_error (!*!id, !*@id))
      end
  | EConstr _ ->   raise (WrongType (OTState None, OTNetlist None, !@e, ErSimple))
  | EContinue _ -> raise (WrongType (OTStateTransition None, OTNetlist None, !@e, ErSimple))
  | ERestart _ ->  raise (WrongType (OTStateTransition None, OTNetlist None, !@e, ErSimple))
  | ESupOp (op, args) when !!op = "concat" -> begin
      let dimensioned, dim_args = List.fold_left_map (exp fun_env) dimensioned args in
      let arg1, arg2 = match dim_args with
        | [arg1; arg2] -> arg1, arg2
        | _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, 2, !!op)
      in
      let n1, n2 = match !%%arg1, !%%arg2 with
        | NProd _, _ -> raise @@ (* Errors. *)UnexpectedProd (!%@arg1, ProdOp !!op)
        | _, NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@arg2, ProdOp !!op)
        | NDim n1, NDim n2 ->
            if abs (n1 - n2) > 1 then
              raise @@ (* Errors. *)WrongDimension (!%%arg2, !%%arg1, !%@arg2, ErOp (!!op, !%@arg1))
            else n1, n2
      in
      dimensioned, concat op !@e (arg1, n1) (arg2, n2)
      end
  | ESupOp (op, args) when !!op = "add_dim" -> begin
      let dimensioned, dim_args = List.fold_left_map (exp fun_env) dimensioned args in
      let arg = match dim_args with
        | [arg] -> arg
        | _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, 1, !!op)
      in
      let dim = match !%%arg with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@arg, ProdOp !!op)
        | NDim n -> n
      in
      dimensioned, dimension (supop op (dim_args) dim) !@e (NDim (dim+1))
      end
  | ESupOp (op, args) ->
      let special_arg, args =
        if !!op = "mux" then
          try [List.hd args], List.tl args with Failure _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, 3, !!op)
        else
          [], args
      in
      let f d arg =
        try
          let d, res = exp fun_env d arg in
          d, Ok res
        with CannotDimensionYet id -> d, Error id
      in
      let dimensioned, test_dim_args = List.fold_left_map f dimensioned args in
      let dim_ex = List.find_opt Result.is_ok test_dim_args in
      let dim_ex = match dim_ex with
      | None -> raise @@ CannotDimensionYet (Result.get_error @@ List.hd test_dim_args)
      | Some dim_ex -> Result.get_ok dim_ex
      in
      let dim = match !%%dim_ex with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@dim_ex, ProdOp !!op)
        | NDim n -> n
      in
      let f dim dimensioned arg =
        try
          assert_exp fun_env (NDim dim) dimensioned arg
        with (* Errors. *)WrongDimension (n1, n2, loc1, ErSimple) -> raise @@ (* Errors. *)WrongDimension (n1, n2, loc1, ErOp (!!op, !%@dim_ex))
      in
      let dimensioned, dim_special_arg = List.fold_left_map (f 0) dimensioned special_arg in
      let dimensioned, dim_args = List.fold_left_map (f dim) dimensioned args in
      dimensioned, dimension (supop op (dim_special_arg @ dim_args) dim) !@e (NDim dim)
  | ESlice (params, e1) ->
      let dimensioned, e1 = exp fun_env dimensioned e1 in
      let dim = match !%%e1 with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@e1, ProdOp "slice")
        | NDim n -> n
      in
      let dim, exp = try slice params !@e dim with Errors.TmpError -> raise @@ Errors.SliceTooMuch (dim, List.length params, !%@e1) in
      dimensioned, dimension (exp e1) !@e dim
  | EReg e1 ->
      let dimensioned, e1 = exp fun_env dimensioned e1 in
      let dim = match !%%e1 with
        | NProd _ -> raise @@ (* Errors. *)UnexpectedProd (!%@e1, ProdOp "reg")
        | NDim n -> NDim n
      in
      dimensioned, dimension (EReg e1) !@e dim
  | ECall (fname, params, args) ->
      let dims_in, dims_out = Misc.option_get ~error:(Errors.Scope_error (!!fname, !@fname)) @@ FunEnv.find_opt !!fname fun_env in
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
        with Invalid_argument _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, List.length dims_in, !!fname)
      in
      dimensioned, dimension (ECall (fname, params, dim_args)) !@e dims_out
  | EMem (mem_kind, (addr_size, word_size, input_file), args) ->
      let fname, dims_in, dims_out = match !!mem_kind with MRom -> "rom", [NDim 1], NDim 1 | MRam -> "ram", [NDim 1; NDim 0; NDim 1; NDim 1], NDim 1 in
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
        with Invalid_argument _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, List.length dims_in, fname)
      in
      dimensioned, dimension (EMem (mem_kind, (addr_size, word_size, input_file), dim_args)) !@e dims_out

and assert_exp fun_env dim dimensioned e =
  try
    let dimensioned, res = exp fun_env dimensioned e in
    if dim <> !%%res then raise @@ (* Errors. *)WrongDimension (!%%res, dim, !@e, ErSimple);
    dimensioned, res
  with CannotDimensionYet id -> match !!e with
  | EConst _ -> failwith "Cannot fail to dimension a constant"
  | EConstr _
  | EContinue _
  | ERestart _ -> failwith "Should already be excluded"
  | EVar id -> begin
      try
        match Env.find !**id dimensioned with
        | Some (BState _ | BStateTransition _ as ti) -> raise (WrongType (ot_of_t ti, OTNetlist None, !@e, ErRev))
        | Some BNetlist dim' when dim <> dim' ->
            raise @@ (* Errors. *)WrongDimension (dim', dim, !@e, ErSimple)
        | None ->
            Env.add !**id (Some (BNetlist dim)) dimensioned, dimension (EVar id) !@e dim
        | Some BNetlist dim' ->
            dimensioned, dimension (EVar id) !@e dim'
      with Not_found -> raise (Errors.Scope_error (!*!id, !*@id))
      end
  | ESupOp (op, _) when !!op = "concat" -> begin
      match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp (!!op), None)
        | NDim _ -> raise (CannotDimensionYet id)
      end
  | ESupOp (op, args) when !!op = "dim_add" ->
      let dim_int = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp (!!op), None)
        | NDim 0 -> raise @@ (* Errors. *)ImpossibleDimension (NDim 0, !@e)
        | NDim n -> n
      in
      let dimensioned, dim_args = List.fold_left_map (assert_exp fun_env (NDim (dim_int - 1))) dimensioned args in
      dimensioned, dimension (supop op dim_args dim_int) !@e dim
  | ESupOp (op, args) when !!op = "mux" ->
      let dim_int = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp (!!op), None)
        | NDim n -> n
      in
      let special_arg, args =
        try List.hd args, List.tl args with Failure _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, 3, !!op)
      in
      let dimensioned, dim_spe_arg = assert_exp fun_env (NDim 0) dimensioned special_arg in
      let dimensioned, dim_args = List.fold_left_map (assert_exp fun_env dim) dimensioned args in
      dimensioned, dimension (supop op (dim_spe_arg :: dim_args) dim_int) !@e dim
  | ESupOp (op, args) ->
      let dim_int = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp (!!op), None)
        | NDim n -> n
      in
      let dimensioned, dim_args = List.fold_left_map (assert_exp fun_env dim) dimensioned args in
      dimensioned, dimension (supop op dim_args dim_int) !@e dim
  | ESlice (params, e1) ->
      let dim_int_pre = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp "slice", None)
        | NDim n -> n
      in
      let slice_dim_removed = function
        | SliceAll ->       0
        | SliceOne _ ->     1
        | SliceFrom _ ->    0
        | SliceTo _ ->      0
        | Slice _ ->        0
      in
      let dims_removed = List.fold_left (fun acc el -> acc + slice_dim_removed el) 0 params in
      let dim_int = dim_int_pre + dims_removed in
      let dimensioned, e1 = assert_exp fun_env (NDim dim_int) dimensioned e1 in
      let dim', exp = try slice params !@e dim_int with Errors.TmpError -> failwith "Problem in computations in backwards slice" in
      if dim <> dim' then failwith "Problem in computations in backwards slice";
      dimensioned, dimension (exp e1) !@e dim'
  | EReg e1 ->
      let dim = match dim with
        | NProd _ -> raise @@ (* Errors. *)ImpossibleProd (!@e, ProdOp "reg", None)
        | NDim n -> NDim n
      in
      let dimensioned, e1 = assert_exp fun_env dim dimensioned e1 in
      dimensioned, dimension (EReg e1) !@e !%%e1
  | ECall _
  | EMem _ ->
     raise (CannotDimensionYet id) (* The dimension of the result does not give further info to dimension the arguments *)

let rec lvalue0 dimensioned (lval: CommonAST.lvalue0) = match !!lval with
  | LValDrop -> raise (CannotDimensionYet None)
  | LValId id -> begin
      try
        match Env.find !**id dimensioned with
        | None -> raise (CannotDimensionYet (Some id))
        | Some dim -> tritype (LValId id) !@lval dim
      with Not_found -> failwith "Variable not properly added"
      end
  | LValTuple l ->
      let dim_l = List.map (lvalue0 dimensioned) l in
      let extract dim = match !??dim with
      | BNetlist n -> n
      | _ -> failwith "Not implemented mixed state / netlist tuples"
      in
      let dim = List.map extract dim_l in
      tritype (LValTuple dim_l) !@lval (BNetlist (NProd dim))

let rec assert_lvalue0 dim dimensioned (lval: CommonAST.lvalue0) = match !!lval with
  | LValDrop -> dimensioned, tritype LValDrop !@lval dim
  | LValId id -> begin
      try
        match Env.find !**id dimensioned with
        | Some dim' when dim <> dim' ->
            raise @@ (* Errors. *)WrongType (ot_of_t dim', ot_of_t dim, !@lval, ErRev)
        | None ->
            Env.add !**id (Some dim) dimensioned, tritype (LValId id) !@lval dim
        | Some dim' ->
            dimensioned, tritype (LValId id) !@lval dim'
      with Not_found -> failwith "Variable not properly added"
      end
  | LValTuple l ->
      let dim_l = match dim with
        | BNetlist NProd dim_l -> List.map (fun d -> BNetlist d) dim_l
        | BNetlist NDim _ -> raise @@ (* Errors. *)ImpossibleProd (!@lval, ProdRev, None)
        | _ -> failwith "Not implemented mixed state / netlist tuples"
      in
      let dimensioned, dimed_l = Misc.fold_left_map2 (fun dimensioned dim lval -> assert_lvalue0 dim dimensioned lval) dimensioned dim_l l in
      let extract dim = match !??dim with
      | BNetlist n -> n
      | _ -> failwith "Not implemented mixed state / netlist tuples"
      in
      let dim = List.map extract dimed_l in
      dimensioned, tritype (LValTuple dimed_l) !@lval (BNetlist (NProd dim))



let rec state_exp (exp_env, enum_env as env) dimensioned (e: StaticTypedAST.exp) = match !!e with
  | EConstr c ->
      dimensioned, state_type (ESConstr c) !@e (Misc.option_get ~error:(Failure "enum_env") @@ ConstructEnv.find_opt !**c enum_env)
  | ESupOp (op, args) when !!op = "mux" -> begin
      let arg1, arg2, arg3 = match args with
        | [arg1; arg2; arg3] -> arg1, arg2, arg3
        | _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, 3, !!op)
      in
      let dimensioned, a = assert_exp exp_env (NDim 0) dimensioned arg1 in
      let dimensioned, b = state_exp env dimensioned arg2 in
      let dimensioned, c = state_exp env dimensioned arg3 in
      if !**(b.s_type.enum_name) <> !**(c.s_type.enum_name) then
        raise @@ WrongType (ot_of_t (BState c.s_type), ot_of_t (BState b.s_type), c.s_loc, ErSimple);
      dimensioned, state_type (ESMux (a, b, c)) !@e b.s_type
    end
  | EReg a ->
      let dimensioned, e' = state_exp env dimensioned a in
      dimensioned, state_type (ESReg e') !@e e'.s_type
  | EVar id -> begin
      try
        match Env.find !**id dimensioned with
        | None -> raise (CannotDimensionYet (Some id))
        | Some BState s -> dimensioned, state_type (ESVar id) !@e s
        | Some (BNetlist _ | BStateTransition _ as ti) -> raise (WrongType (ot_of_t ti, OTState None, !@e, ErSimple))
      with Not_found -> raise (Errors.Scope_error (!*!id, !*@id))
    end
  | EContinue _ ->  raise @@ WrongType (OTStateTransition None, OTState None, !@e, ErSimple)
  | ERestart _ ->   raise @@ WrongType (OTStateTransition None, OTState None, !@e, ErSimple)
  | EConst _ ->     raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | ESupOp _ ->     raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | ESlice _ ->     raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | ECall _ ->      raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | EMem _ ->       raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)

let rec assert_state_exp (exp_env, enum_env as env) s dimensioned (e: StaticTypedAST.exp) = match !!e with
  | EConstr c ->
      let s' = Misc.option_get ~error:(Failure "enum_env") @@ ConstructEnv.find_opt !**c enum_env in
      if s <> s' then raise @@ WrongType (ot_of_t (BState s'), ot_of_t (BState s), !@e, ErRev);
      dimensioned, state_type (ESConstr c) !@e s'
  | ESupOp (op, args) when !!op = "mux" -> begin
      let arg1, arg2, arg3 = match args with
        | [arg1; arg2; arg3] -> arg1, arg2, arg3
        | _ -> raise @@ Errors.WrongNumberArguments (List.length args, !@e, 3, !!op)
      in
      let dimensioned, a = assert_exp exp_env (NDim 0) dimensioned arg1 in
      let dimensioned, b = assert_state_exp env s dimensioned arg2 in
      let dimensioned, c = assert_state_exp env s dimensioned arg3 in
      dimensioned, state_type (ESMux (a, b, c)) !@e s
    end
  | EReg a ->
      let dimensioned, e' = assert_state_exp env s dimensioned a in
      dimensioned, state_type (ESReg e') !@e s
  | EVar id -> begin
      try
        match Env.find !**id dimensioned with
        | Some (BNetlist _ | BStateTransition _ as ti) -> raise (WrongType (ot_of_t ti, OTState None, !@e, ErRev))
        | Some BState s' when s <> s' ->
            raise @@ WrongType (ot_of_t (BState s'), ot_of_t (BState s), !@e, ErRev)
        | None ->
            Env.add !**id (Some (BState s)) dimensioned, state_type (ESVar id) !@e s
        | Some BState _ ->
            dimensioned, state_type (ESVar id) !@e s
      with Not_found -> raise (Errors.Scope_error (!*!id, !*@id))
    end
  | EContinue _ ->  raise @@ WrongType (OTStateTransition None, OTState None, !@e, ErSimple)
  | ERestart _ ->   raise @@ WrongType (OTStateTransition None, OTState None, !@e, ErSimple)
  | EConst _ ->     raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | ESupOp _ ->     raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | ESlice _ ->     raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | ECall _ ->      raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)
  | EMem _ ->       raise @@ WrongType (OTNetlist None, OTState None, !@e, ErSimple)



let state_transition_exp env dimensioned (e: StaticTypedAST.exp) = match !!e with
  | EContinue e' ->
      let dimensioned, e' = state_exp env dimensioned e' in
      dimensioned, state_transition_type (ESTContinue e') !@e e'.s_type
  | ERestart e' ->
      let dimensioned, e' = state_exp env dimensioned e' in
      dimensioned, state_transition_type (ESTRestart e') !@e e'.s_type
  | EConstr _ ->    raise @@ WrongType (OTState None,   OTStateTransition None, !@e, ErSimple)
  | EConst _ ->     raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | EVar _ ->       raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | ESupOp _ ->     raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | ESlice _ ->     raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | EReg _ ->       raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | ECall _ ->      raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | EMem _ ->       raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)

let assert_state_transition_exp env s dimensioned (e: StaticTypedAST.exp) = match !!e with
  | EContinue e' ->
      let dimensioned, e' = assert_state_exp env s dimensioned e' in
      dimensioned, state_transition_type (ESTContinue e') !@e s
  | ERestart e' ->
      let dimensioned, e' = assert_state_exp env s dimensioned e' in
      dimensioned, state_transition_type (ESTRestart e') !@e s
  | EConstr _ ->    raise @@ WrongType (OTState None,   OTStateTransition None, !@e, ErSimple)
  | EConst _ ->     raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | EVar _ ->       raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | ESupOp _ ->     raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | ESlice _ ->     raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | EReg _ ->       raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | ECall _ ->      raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)
  | EMem _ ->       raise @@ WrongType (OTNetlist None, OTStateTransition None, !@e, ErSimple)

let tritype_exp (exp_env, _ as env) dimensioned e =
  let f f_exp env = try Ok (f_exp env dimensioned e) with WrongType e -> Error e in
  match f exp exp_env, f state_exp env, f state_transition_exp env with
  | Ok (dimensioned, a), Error _, Error _ -> dimensioned, Exp a
  | Error _, Ok (dimensioned, b), Error _ -> dimensioned, StateExp b
  | Error _, Error _, Ok (dimensioned, c) -> dimensioned, StateTransitionExp c
  | _ -> raise @@ Errors.TwoTypes !@e


let tritype_of_exp = function
  | Exp e -> BNetlist !%%e
  | StateExp e -> BState e.s_type
  | StateTransitionExp e -> BStateTransition e.st_type


let result_fold2 ~oks r1 r2 =
  Misc.result_fold2 ~oks:oks ~errors:(fun a b -> if Option.is_some a then a else b) ~mixed1:(fun _ e -> Error e) ~mixed2:(fun e _ -> Error e) r1 r2

let assert_exp_one fun_env dim (dimensioned: dim_env) e : dim_env * exp dimension_option =
  try
    let dimensioned, e' = assert_exp fun_env dim dimensioned e in
    dimensioned, Ok e'
  with CannotDimensionYet id -> dimensioned, Error id

let assert_state_exp_one env s (dimensioned: dim_env) e : dim_env * exp state_exp dimension_option =
  try
    let dimensioned, e' = assert_state_exp env s dimensioned e in
    dimensioned, Ok e'
  with CannotDimensionYet id -> dimensioned, Error id

let assert_state_transition_exp_one env s (dimensioned: dim_env) e : dim_env * exp state_transition_exp dimension_option =
  try
    let dimensioned, e' = assert_state_transition_exp env s dimensioned e in
    dimensioned, Ok e'
  with CannotDimensionYet id -> dimensioned, Error id


let assert_tritype_exp_one (exp_env, _ as env) dim (dimensioned: dim_env) e : dim_env * tritype_exp dimension_option =
  match dim with
  | BNetlist ti ->
      let dimensioned, e' = assert_exp_one exp_env ti dimensioned e in
      dimensioned, Result.map (fun e -> Exp e) e'
  | BState s ->
      let dimensioned, e' = assert_state_exp_one env s dimensioned e in
      dimensioned, Result.map (fun e -> StateExp e) e'
  | BStateTransition s ->
      let dimensioned, e' = assert_state_transition_exp_one env s dimensioned e in
      dimensioned, Result.map (fun e -> StateTransitionExp e) e'


let tritype_exp_one fun_env (dimensioned: dim_env) e : dim_env * tritype_exp dimension_option =
  try
    let dimensioned, e' = tritype_exp fun_env dimensioned e in
    dimensioned, Ok e'
  with CannotDimensionYet id -> dimensioned, Error id

let state_exp_one fun_env (dimensioned: dim_env) e : dim_env * exp state_exp dimension_option =
  try
    let dimensioned, e' = state_exp fun_env dimensioned e in
    dimensioned, Ok e'
  with CannotDimensionYet id -> dimensioned, Error id

let state_transition_exp_one fun_env (dimensioned: dim_env) e : dim_env * exp state_transition_exp dimension_option =
  try
    let dimensioned, e' = state_transition_exp fun_env dimensioned e in
    dimensioned, Ok e'
  with CannotDimensionYet id -> dimensioned, Error id

let lvalue_one dimensioned StaticTypedAST.{ lval; lval_type } =
  try
    let dimensioned, lval' = match !!lval_type with
    | Some ti -> assert_lvalue0 (global_of_netlist_type ti) dimensioned lval
    | None ->    dimensioned, lvalue0 dimensioned lval
    in
    dimensioned, Ok { lval = lval'; lval_type }
  with CannotDimensionYet id -> (dimensioned, Error id)

let assert_lvalue_one dim dimensioned StaticTypedAST.{ lval; lval_type } =
  let () = match !!lval_type with
  | Some ti -> if dim <> global_of_netlist_type ti then
      raise @@ (* Errors. *)WrongIndication (ot_of_t dim, ot_of_t @@ global_of_netlist_type ti, !@lval_type, ErSimple)
  | None -> ()
  in
  try
    let dimensioned, lval' = assert_lvalue0 dim dimensioned lval in
    dimensioned, Ok { lval = lval'; lval_type }
  with CannotDimensionYet id -> (dimensioned, Error id)

let eq_one fun_env dimensioned (lval, e) =
  let dimensioned, e' = tritype_exp_one fun_env dimensioned e in
  let dimensioned, lval' = match e' with
    | Ok a -> assert_lvalue_one (tritype_of_exp a) dimensioned lval
    | Error _ -> lvalue_one dimensioned lval
  in
  let dimensioned, e' = match lval' with
    | Ok a -> assert_tritype_exp_one fun_env !??(a.lval) dimensioned e
    | Error _ -> dimensioned, e'
  in
  dimensioned, (lval', e')

let rec match_handler_one fun_env dimensioned ({ m_body; _} as handler) =
  let dimensioned, m_body' = block_one fun_env dimensioned m_body in
  dimensioned, Result.map (fun m_body -> { handler with m_body }) m_body'

and matcher_one fun_env dimensioned ({ m_handlers; m_state_type; _ } as matcher) : dim_env * state_type * decl matcher dimension_option =
  let dimensioned, m_handlers' = constructenv_map_fold1 (match_handler_one fun_env) dimensioned m_handlers in
  dimensioned, m_state_type, Result.map (fun m_handlers -> { matcher with m_handlers }) m_handlers'

and transition_one (fun_env, _ as env) dimensioned : 'a -> 'b * 'c dimension_option = function
  | [] -> dimensioned, Ok []
  | hd :: tl ->
      let dimensioned, hd1' = assert_exp_one fun_env (NDim 0) dimensioned (fst hd) in
      let dimensioned, hd2' = state_transition_exp_one env dimensioned (snd hd) in
      let dimensioned, tl' = transition_one env dimensioned tl in
      let hd' = result_fold2 ~oks:(fun a b -> a, b) hd1' hd2' in
      dimensioned, result_fold2 ~oks:(fun hd tl -> hd :: tl) hd' tl'

and automaton_handler_one env dimensioned ({ a_body; a_weak_transition; a_strong_transition; _ } as handler) =
  let dimensioned, a_body' = block_one env dimensioned a_body in
  let dimensioned, a_weak_transition' = transition_one env dimensioned a_weak_transition in
  let dimensioned, a_strong_transition' = transition_one env dimensioned a_strong_transition in
  let transitions' = result_fold2 ~oks:(fun a b -> (a, b)) a_weak_transition' a_strong_transition' in
  dimensioned, result_fold2 ~oks:(fun a_body (a_weak_transition, a_strong_transition) ->
    { handler with a_body; a_weak_transition; a_strong_transition})
    a_body' transitions'

and automaton_one env dimensioned ({ a_handlers; _} as auto: StaticTypedAST.automaton) : dim_env * automaton dimension_option =
  let dimensioned, a_handlers' = constructenv_map_fold2 (automaton_handler_one env) dimensioned a_handlers in
  dimensioned, Result.map (fun a_handlers -> { auto with a_handlers }) a_handlers'

and decl_one (fun_env, _ as env) dimensioned (d: StaticTypedAST.decl) : dim_env * decl dimension_option = match !!d with
  | Deq (lval, e) ->
      let dimensioned, (lval', e') = eq_one env dimensioned (lval, e) in
      dimensioned, (result_fold2 ~oks:(fun a b -> relocalize !@d @@ Deq (a, b)) lval' e')
  | Dlocaleq (lval, e) ->
      let dimensioned, (lval', e') = eq_one env dimensioned (lval, e) in
      dimensioned, (result_fold2 ~oks:(fun a b -> relocalize !@d @@ Dlocaleq (a, b)) lval' e')
  | Dif (c, b1, b2) ->
      let dimensioned, b1' = block_one env dimensioned b1 in
      let dimensioned, b2' = block_one env dimensioned b2 in
      dimensioned, (result_fold2 ~oks:(fun b1 b2 -> relocalize !@d @@ Dif (c, b1, b2)) b1' b2')
  | Dreset (e, b) ->
      let dimensioned, e' = assert_exp_one fun_env (NDim 0) dimensioned e in
      let dimensioned, b' = block_one env dimensioned b in
      dimensioned, (result_fold2 ~oks:(fun e b -> relocalize !@d @@ Dreset (e, b)) e' b')
  | Dmatch (e, m) ->
      let dimensioned, s, m' = matcher_one env dimensioned m in
      let dimensioned, e' = assert_state_exp_one env s dimensioned e in
      dimensioned, (result_fold2 ~oks:(fun e m -> relocalize !@d @@ Dmatch (e, m)) e' m')
  | Dautomaton a ->
      let dimensioned, a' = automaton_one env dimensioned a in
      dimensioned, (Result.map (fun a -> relocalize !@d @@ Dautomaton a) a')

and constructenv_map_fold1 handler_one dimensioned s_handlers =
  ConstructEnv.fold
    (fun uid handler (dimensioned, re_handlers') ->
      let dimensioned, handler' = handler_one dimensioned handler in
      dimensioned, result_fold2 ~oks:(fun handler re_handlers -> ConstructEnv.add uid handler re_handlers) handler' re_handlers'
    ) s_handlers (dimensioned, Ok ConstructEnv.empty)

and constructenv_map_fold2 handler_one dimensioned s_handlers = (* Typing would not le me use the same function twice *)
  ConstructEnv.fold
    (fun uid handler (dimensioned, re_handlers') ->
      let dimensioned, handler' = handler_one dimensioned handler in
      dimensioned, result_fold2 ~oks:(fun handler re_handlers -> ConstructEnv.add uid handler re_handlers) handler' re_handlers'
    ) s_handlers (dimensioned, Ok ConstructEnv.empty)

and block_one fun_env dimensioned : StaticTypedAST.decl list -> dim_env * decl list dimension_option = function
  | [] -> dimensioned, Ok []
  | hd :: tl ->
      let dimensioned, hd' = decl_one fun_env dimensioned hd in
      let dimensioned, tl' = block_one fun_env dimensioned tl in
      dimensioned, result_fold2 ~oks:List.cons hd' tl'

let body fun_env (name, loc) dimensioned b =
  let rec one (dimensioned, b) =
    let (dimensioned', b') = block_one fun_env dimensioned b in
    match b' with
    | Ok a ->
        let dimensioned = Env.map (Misc.option_get ~error:(Failure "We can dimension everything, but not all variables are dimensioned?")) dimensioned' in
        dimensioned, a
    | Error _ when dimensioned <> dimensioned' ->
        one (dimensioned', b)
    | Error Some id ->
        Errors.raise_warning_dimension (Errors.InsufficientAnnotations (!!name, loc, !*!id));
        one (Env.add !**id (Some (BNetlist (NDim 0))) dimensioned', b)
    | Error None ->
        failwith "We can have all variables dimensioned, but not be able to dimension everything?"
  in
  one (dimensioned, b)

let true_global_of_netlist_type = function
  | BNetlist ti -> (dimension_of_netlist_type ti)
  | _ -> failwith "Not implemented state arguments in functions"

let starput dimensioned { ti_name; ti_type; _ } : dim_env =
  Env.add !**ti_name (Some (global_of_netlist_type !!ti_type)) dimensioned

let fun_env { node_inputs; node_outputs; _ } =
  List.map (fun input -> true_global_of_netlist_type !!(input.ti_type)) node_inputs,
  match List.map (fun input -> true_global_of_netlist_type !!(input.ti_type)) node_outputs with
  | [out] -> out
  | l -> NProd l


let node fun_env ({ node_inputs; node_outputs; node_body; node_variables; node_name; node_loc; _ } as node) : node =
  let dimensioned = Env.map (fun _ -> None) node_variables in
  let dimensioned = List.fold_left starput dimensioned node_inputs in
  let dimensioned = List.fold_left starput dimensioned node_outputs in

  let node_variables0, node_body = body fun_env (node_name, node_loc) dimensioned node_body in
  let node_variables = Env.mapi (fun key ti -> let id = Env.find key node_variables in tritype id !*@id ti) node_variables0 in

  { node with
    node_inputs;
    node_outputs;
    node_body;
    node_variables
  }

let program ({ p_nodes; p_enums; _ } as program) : program =
  try
    let fun_env = FunEnv.map fun_env p_nodes in
    { program with
      p_nodes = FunEnv.map (node (fun_env, p_enums)) p_nodes;
    }
  with
  | Errors.SliceTooMuch (found, expected, loc) ->
      Format.eprintf "%aType Error: This expression has dimension %i but it is sliced %i times@."
        Location.print_location loc
        found expected;
      raise Errors.ErrorDetected
  | UnexpectedProd (loc, _) ->
      Format.eprintf "%aType Error: This expression is a tuple, but no tuple were expected@.@."
        Location.print_location loc;
      raise Errors.ErrorDetected
  | WrongIndication (found, hint, loc, _) ->
      Format.eprintf "%aType Error: This hint indicates a type %t but an expression of type %t was found@."
        Location.print_location loc
        (print_ot hint)
        (print_ot found);
      raise Errors.ErrorDetected
  | WrongType (found, expected, loc, _) ->
      Format.eprintf "%aType Error: This expression has type %t but an expression of type %t was expected@."
        Location.print_location loc
        (print_ot found)
        (print_ot expected);
      raise Errors.ErrorDetected
  | WrongDimension (found, expected, loc, _) ->
      Format.eprintf "%aType Error: This expression has type %t but an expression of type %t was expected@."
        Location.print_location loc
        (print_netlist_dimension found)
        (print_netlist_dimension expected);
      raise Errors.ErrorDetected
  | Errors.WrongNumberArguments (found, loc, expected, fname) ->
      Format.eprintf "%aType Error: Function %s has %i arguments but %i were given@."
        Location.print_location loc fname expected found;
      raise Errors.ErrorDetected

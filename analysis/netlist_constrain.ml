open CommonAST
open StaticTypedPartialAST
open NetlistDimensionedAST
open NetlistConstrainedAST

let rec other_context fname loc ctxt = function
  | TProd l -> TProd (List.map (other_context fname loc ctxt) l)
  | TNDim l -> TNDim (List.map (fun p -> PSOtherContext (fname, loc, ctxt, p)) l)

let rec eq_to_constraints c1 c2 = match c1, c2 with
  | TProd l1, TProd l2 -> List.flatten @@ List.rev_map2 eq_to_constraints l1 l2
  | TNDim l1, TNDim l2 ->  List.combine l1 l2
  | TNDim _,  TProd _
  | TProd _,  TNDim _ ->   failwith "Misdimensioned value"


let fun_env_find fun_env id =
  let reloc a = relocalize !@id a in
  let regexp_slice = Str.regexp {|slice\(\(_\(all\|one\|to\|from\|fromto\)\)*\)|} in
  let regexp_supop = Str.regexp {|\(or\|and\|xor\|nand\|nor\|not\|mux\|concat\|add_dim\)_\([0-9]+\)|} in
  if FunEnv.mem !!id fun_env then
    FunEnv.find !!id fun_env
  else if Str.string_match regexp_slice !!id 0 then begin
    let args = List.tl @@ String.split_on_char '_' @@ Str.matched_group 1 !!id in
    let dim = List.length args in
    let dims_in = List.init dim (fun i -> PSConst (reloc (SIParam i))) in
    let rec aux idim iparam = function
      | "all"  :: tl ->   PSConst (reloc (SIParam idim)) :: aux (idim+1) iparam tl
      | "one"  :: tl ->                                  aux idim (iparam+1) tl
      | "from" :: tl ->   PSConst (reloc (SIBinOp (SAdd, reloc (SIBinOp (SMinus, reloc (SIBinOp (SMinus, reloc (SIParam idim), reloc (SInt 1))), reloc (SIParam iparam))), reloc (SInt 1)))) :: aux (idim+1) (iparam+1) tl
      | "to"   :: tl ->   PSConst (reloc (SIBinOp (SAdd, reloc (SIParam iparam), reloc (SInt 1)))) :: aux (idim+1) (iparam+1) tl
      | "fromto" :: tl -> PSConst (reloc (SIBinOp (SAdd, reloc (SIBinOp (SMinus, reloc (SIParam (iparam+1)), reloc (SIParam iparam))), reloc (SInt 1)))) :: aux (idim+1) (iparam+2) tl
      | [] -> []
      | _ -> failwith "Miscounted arguments in slice"
    in
    let dims_out = TNDim (aux 0 dim args) in
    [TNDim dims_in], dims_out
  end else if Str.string_match regexp_supop !!id 0 then begin
    let op = Str.matched_group 1 !!id in
    let dim = int_of_string @@ Str.matched_group 2 !!id in
    let dims_in_list = List.init dim (fun i -> PSConst (reloc (SIParam i))) in
    let dims_in = TNDim dims_in_list in
    if op = "concat" then begin
      if dim < 1 then failwith "Undefined function in presizing";
      let tail_in = List.init (dim-1) (fun i -> PSConst (reloc (SIParam (i+2)))) in
      [TNDim (PSConst (reloc (SIParam 0)) :: tail_in); TNDim (PSConst (reloc (SIParam 1)) :: tail_in)],
      TNDim (PSConst (reloc (SIBinOp (SAdd, reloc (SIParam 0), reloc (SIParam 1)))) :: tail_in)
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
  let addr_size = PSConst (relocalize !@mem_kind (SIParam 0)) in
  let word_size = PSConst (relocalize !@mem_kind (SIParam 1)) in
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
  | NetlistDimensionedAST.EVar id ->
      let size = Misc.option_get ~error:(Failure "Undefined variable in presizing") @@ Env.find_opt !**id var_env in
      constraints, presize (EVar id) !%@e size
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

let rec dim_to_blank_presize s = function
  | NDim n ->  TNDim  (List.init n (fun i -> PSVar (s, i, UIDUnknownStatic.get ())))
  | NProd l -> TProd (List.map (dim_to_blank_presize s) l)

let rec lvalue var_env lval = match !%!lval with
  | LValDrop ->
      presize LValDrop !%@lval (dim_to_blank_presize (relocalize !%@lval "_") !%%lval)
  | LValId id ->
      let size = Misc.option_get ~error:(Failure "Undefined variable in presizing") @@ Env.find_opt !!id var_env in
      presize (LValId id) !%@lval size
  | LValTuple l ->
      let size_l = List.map (lvalue var_env) l in
      let size = List.map (!&&) size_l in
      presize (LValTuple size_l) !%@lval (TProd size)


let eqs fun_env var_env0 NetlistDimensionedAST.{ equations } =
  let rec add_vars_lvalue var_env lvalue = match !%!lvalue with
    | NetlistDimensionedAST.LValDrop -> var_env
    | NetlistDimensionedAST.LValId id -> if Env.mem !!id var_env then var_env else Env.add !!id (dim_to_blank_presize id !%%lvalue) var_env
    | NetlistDimensionedAST.LValTuple l -> List.fold_left add_vars_lvalue var_env l
  in
  let var_env = List.fold_left (fun s eq -> (add_vars_lvalue s !!eq.NetlistDimensionedAST.eq_left)) var_env0 equations in

  let eq constraints equation =
    let NetlistDimensionedAST.{ eq_left; eq_right } = !!equation in
    let constraints, eq_right = exp (fun_env, var_env) constraints eq_right in
    let eq_left = lvalue var_env eq_left in
    let new_constraints = eq_to_constraints !&&eq_left !&&eq_right in
    new_constraints @ constraints, relocalize !@equation { eq_left; eq_right }
  in
  let constraints, presized_equations = List.fold_left_map eq [] equations in

  List.rev constraints, { dim_env = var_env; equations = presized_equations }



let rec body fun_env name var_env e = match !!e with
  | NetlistDimensionedAST.BIf (condition, block1, block2) ->
      let constraints, body1 = body fun_env name var_env block1 in
      let constraints2, body2 = body fun_env name var_env block2 in
      constraints @ constraints2, relocalize !@e @@ BIf (condition, body1, body2)
  | NetlistDimensionedAST.BEqs case ->
      let (r, eqs) = eqs fun_env var_env case in
      r, relocalize !@e @@ BEqs eqs

let node (var_env_env, sized_inouts_env, fun_env) name NetlistDimensionedAST.{ node_name_loc; node_loc; node_params; node_inline; node_body; node_probes; _ } =
  let var_env0 = Env.find name var_env_env in
  let node_inputs, node_outputs = Env.find name sized_inouts_env in
  let constraints, node_body = body fun_env name var_env0 node_body in
  constraints,
  {
    node_inputs;
    node_outputs;
    node_body;
    node_name_loc; node_loc; node_inline; node_params; node_probes
  }

let rec presize_of_netlist_type ident = function
  | StaticTypedAST.TProd l -> TProd (List.map (presize_of_netlist_type ident) l)
  | StaticTypedAST.TNDim l -> TNDim (List.mapi
      (fun i opt_static_exp -> match !!opt_static_exp with
        | SUnknown uid -> PSVar (ident, i, uid)
        | SExp se -> PSConst (relocalize !@opt_static_exp se)
        ) l
      )

let starput NetlistDimensionedAST.{desc = { name; typed; _ }; loc } =
  (!!name, presize_of_netlist_type name !!typed),
  relocalize loc { name; presize = relocalize !@typed @@ presize_of_netlist_type name !!typed }

let fun_env NetlistDimensionedAST.{ node_inputs; node_outputs; _ } =
  let ins = List.map starput node_inputs in
  let outs = List.map starput node_outputs in
  List.fold_left (fun var_env ((name, presize), _) -> Env.add name presize var_env) Env.empty (ins @ outs),
  (List.map snd ins, List.map snd outs),
  (List.map (fun ((_, presize), _) -> presize) ins,
    match List.map (fun ((_, presize), _) -> presize) outs with
      | [out] -> out
      | l -> TProd l
  )

let program NetlistDimensionedAST.{ p_consts; p_consts_order; p_nodes } : program =
  let pre_fun_env = Env.map fun_env p_nodes in
  let var_env_env = Env.map (fun (var_env, _, _) -> var_env) pre_fun_env in
  let sized_inouts_env = Env.map (fun (_, inouts, _) -> inouts) pre_fun_env in
  let fun_env = Env.map (fun (_, _, inout_sizes) -> inout_sizes) pre_fun_env in
  let constraints = ref [] in
  let f nam nod =
    let c, r = node (var_env_env, sized_inouts_env, fun_env) nam nod in
    constraints := c @ !constraints;
    r
  in
  let p_nodes = Env.mapi f p_nodes in
  {
    p_consts; p_consts_order;
    p_nodes; constraints = !constraints
  }

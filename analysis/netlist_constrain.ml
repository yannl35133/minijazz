open CommonAST
open StaticTypedPartialAST
open NetlistDimensionedAST
open NetlistConstrainedAST

let rec dim_to_blank_presize s = function
  | NDim n ->  CDDim  (List.init n (fun i -> PSVar (s, i, UniqueId.get ())))
  | NProd l -> CDProd (List.map (dim_to_blank_presize s) l)

let rec eq_to_constraints c1 c2 = match c1, c2 with
  | CDProd l1, CDProd l2 -> List.flatten @@ List.rev_map2 eq_to_constraints l1 l2
  | CDDim l1,  CDDim l2 ->  List.combine l1 l2
  | CDDim _,   CDProd _
  | CDProd _,  CDDim _ ->   failwith "Misdimensioned value"


let fun_env_find fun_env params loc s =
  let regexp_slice = Str.regexp "slice\\(\\(_\\(all\\|to\\|from\\|fromto\\)\\)*\\)" in
  let regexp_supop = Str.regexp "\\(or\\|and\\|xor\\|nand\\|nor\\|not\\)_\\([0-9]+\\)" in
  if Env.mem s fun_env then
    Env.find s fun_env
  else if Str.string_match regexp_slice s 0 then begin
    let args = List.tl @@ String.split_on_char '_' @@ Str.matched_group 1 s in
    let dim = List.length args in
    let re_params = List.mapi
      (fun i p -> match !!p with
        | SIntExp Some se -> PSConst (relocalize !@p se), !@p
        | SIntExp None ->    PSParam (s, i, UniqueId.get (), loc), loc
        | SBoolExp _ -> failwith "Mistyped slice static argument") params
    in
    let pre_dims_in, rem = let rec nth_tl n = function [] -> [], [] | l when n = 0 -> l, [] | hd :: tl -> let l1, l2 = nth_tl (n - 1) tl in hd :: l1, l2 in nth_tl dim re_params in
    let pre_dims_in = List.map fst pre_dims_in in
    let rec aux i args param = match args, param with
      | "all"  :: tl1,             tl2 -> List.nth pre_dims_in i :: aux (i+1) tl1 tl2
      | "one"  :: tl1, (_, loc) :: tl2 -> PSConst (relocalize loc (SInt 1)) :: aux (i+1) tl1 tl2
      | "from" :: tl1, (p, loc)   :: tl2 -> PSSub (List.nth pre_dims_in i, PSSub (p, PSConst (relocalize loc @@ SInt 1))) :: aux (i+1) tl1 tl2
      | "to"   :: tl1, (p, _)   :: tl2 -> p :: aux (i+1) tl1 tl2
      | "fromto" :: tl1, (p1, _) :: (p2, loc) :: tl2 -> PSSub (p2, PSSub (p1, PSConst (relocalize loc @@ SInt 1))) :: aux (i+1) tl1 tl2
      | [], [] -> []
      | _ -> failwith "Miscounted arguments in slice"
    in
    let dims_out = CDDim (aux 0 args rem) in
    [CDDim pre_dims_in], dims_out
  end else if Str.string_match regexp_supop s 0 then begin
    let op = Str.matched_group 0 s in
    let size_in = CDDim (List.mapi
      (fun i p -> match !!p with
        | SIntExp Some se -> PSConst (relocalize !@p se)
        | SIntExp None ->    PSParam (s, i, UniqueId.get (), loc)
        | SBoolExp _ -> failwith "Mistyped slice static argument")
      params)
    in
    if op = "not" then
      [size_in], size_in
    else
      [size_in; size_in], size_in
  end else
    failwith "Undefined function in presizing"

let rom_ram_size loc (addr_size, word_size, _) = function
  | MRom ->
    let addr_size = match !!addr_size with
      | Some se -> PSConst (relocalize !@addr_size se)
      | None ->    PSParam ("rom", 1, UniqueId.get (), !@addr_size)
    in
    let word_size = match !!word_size with
      | Some se -> PSConst (relocalize !@word_size se)
      | None ->    PSParam ("rom", 2, UniqueId.get (), !@word_size)
    in    
    [CDDim [addr_size]], CDDim [word_size]
  | MRam ->
    let addr_size = match !!addr_size with
      | Some se -> PSConst (relocalize !@addr_size se)
      | None ->    PSParam ("ram", 1, UniqueId.get (), !@addr_size)
    in
    let word_size = match !!word_size with
      | Some se -> PSConst (relocalize !@word_size se)
      | None ->    PSParam ("ram", 2, UniqueId.get (), !@word_size)
    in
    [CDDim [addr_size; PSConst (relocalize loc (SInt 1)); addr_size; word_size]], CDDim [word_size]

let size_value loc v =
  let rec assert_size sizes value = match sizes, value with
    | n :: tl, ParserAST.VNDim l -> if n <> List.length l then raise (Errors.NonConstantSize loc); List.iter (assert_size tl) l
    | [],      ParserAST.VBit _ ->  ()
    | _ :: _,  ParserAST.VBit _ ->  raise (Errors.NonConstantDimension loc)
    | [],      ParserAST.VNDim _ -> raise (Errors.NonConstantDimension loc)
  in
  let rec search_size depth = function
    | ParserAST.VNDim (hd :: tl) -> let r = search_size depth hd in List.iter (assert_size r) tl; (List.length tl + 1) :: r
    | ParserAST.VNDim [] -> raise (Errors.ZeroWideBusMulti (depth, loc))
    | ParserAST.VBit _ -> []
  in
  CDDim (List.map (fun n -> PSConst (relocalize loc (SInt n))) (search_size 0 v))


let rec exp (fun_env, var_env as env) constraints e = match !%!e with
  | NetlistDimensionedAST.EConst c ->
      let size = size_value !%@e c in
      constraints, presize (EConst c) !%@e size
  | NetlistDimensionedAST.EVar id ->
      let size = Misc.option_get ~error:(Failure "Undefined variable in presizing") @@ Env.find_opt !!id var_env in
      constraints, presize (EVar id) !%@e size
  | NetlistDimensionedAST.EReg e1 ->
      let constraints, e1 = exp env constraints e1 in
      let size = match !$$e1 with
        | CDProd _ -> failwith "UnexpectedProd in sizing"
        | CDDim l -> CDDim l
      in
      constraints, presize (EReg e1) !%@e size
  | NetlistDimensionedAST.ECall (fname, params, args) ->
      let dims_in, dims_out = fun_env_find fun_env params !%@e !!fname in
      let constraints, dim_args = List.fold_left_map (exp env) constraints args in
      let new_constraints = List.concat @@ List.rev_map2 eq_to_constraints dims_in @@ List.map (!$$) dim_args in
      new_constraints @ constraints, presize (ECall (fname, params, dim_args)) !%@e dims_out
  | NetlistDimensionedAST.EMem (mem_kind, params, args) ->
      let dims_in, dims_out = rom_ram_size !%@e params !!mem_kind in
      let constraints, dim_args = List.fold_left_map (exp env) constraints args in
      let new_constraints = List.concat @@ List.map2 eq_to_constraints dims_in @@ List.map (!$$) dim_args in
      new_constraints @ constraints, presize (EMem (mem_kind, params, dim_args)) !%@e dims_out


let rec lvalue var_env lval = match !%!lval with
  | NetlistDimensionedAST.LValDrop ->
      presize LValDrop !%@lval (dim_to_blank_presize (relocalize !%@lval "_") !%%lval)
  | NetlistDimensionedAST.LValId id ->
      let size = Misc.option_get ~error:(Failure "Undefined variable in presizing") @@ Env.find_opt !!id var_env in
      presize (LValId id) !%@lval size
  | NetlistDimensionedAST.LValTuple l ->
      let size_l = List.map (lvalue var_env) l in
      let size = List.map (!$$) size_l in
      presize (LValTuple size_l) !%@lval (CDProd size)


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
    let new_constraints = eq_to_constraints !$$eq_left !$$eq_right in
    new_constraints @ constraints, relocalize !@equation { eq_left; eq_right }
  in
  let constraints, presized_equations = List.fold_left_map eq [] equations in

  { dim_env = var_env; equations = presized_equations; constraints }



let rec body fun_env name var_env e = relocalize_fun (function
  | NetlistDimensionedAST.BIf (condition, block1, block2) -> BIf (condition, body fun_env name var_env block1, body fun_env name var_env block2)
  | NetlistDimensionedAST.BEqs case -> BEqs (eqs fun_env var_env case)
  ) e

let rec presize_of_netlist_type ident = function
  | StaticTypedAST.TProd l -> CDProd (List.map (presize_of_netlist_type ident) l)
  | StaticTypedAST.TNDim l -> CDDim (List.mapi
      (fun i opt_static_exp -> match !!opt_static_exp with
        | None -> PSVar (ident, i, UniqueId.get ())
        | Some e -> PSConst (relocalize !@opt_static_exp e)
        ) l
      )

let starput var_env NetlistDimensionedAST.{desc = { name; typed; _ }; loc } =
  Env.add !!name (presize_of_netlist_type name !!typed) var_env,
  relocalize loc { name; presize = relocalize !@typed @@ presize_of_netlist_type name !!typed }

let fun_env NetlistDimensionedAST.{ node_inputs; node_outputs; _ } =
  List.map (fun input -> presize_of_netlist_type !!input.NetlistDimensionedAST.name !!(!!input.typed) ) node_inputs,
  CDProd (List.map (fun input -> presize_of_netlist_type !!input.NetlistDimensionedAST.name !!(!!input.typed)) node_outputs)
  

let node fun_env name NetlistDimensionedAST.{ node_name_loc; node_loc; node_params; node_inline; node_inputs; node_outputs; node_body; node_probes } : node =
  let var_env0 = Env.empty in
  let var_env0, node_inputs  = List.fold_left_map starput var_env0 node_inputs in
  let var_env0, node_outputs = List.fold_left_map starput var_env0 node_outputs in
  {
    node_inputs;
    node_outputs;
    node_body = body fun_env name var_env0 node_body;
    node_name_loc; node_loc; node_inline; node_params; node_probes
  }

let program NetlistDimensionedAST.{ p_consts; p_consts_order; p_nodes } : program =
  let fun_env = Env.map fun_env p_nodes in
  { 
    p_consts; p_consts_order;
    p_nodes = Env.mapi (node fun_env) p_nodes;
  }

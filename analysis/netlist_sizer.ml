open CommonAST
open StaticTypedPartialAST
open NetlistConstrainedAST
open NetlistSizedAST

module UIDEnv = Constraints_solver.UIDEnv
type union_find = Constraints_solver.union_find
let find_opt = Constraints_solver.find_opt

exception CouldNotSize of ident * int
exception CouldNotInfer of ident_desc * Location.location * int

let assert_int = function
  | SIntExp se -> se
  | SBoolExp _ -> failwith "Static type error"
let assert_bool = function
  | SBoolExp se -> se
  | SIntExp _ -> failwith "Static type error"

let rec substitute_int var_env params = function
  | SInt n -> SInt n
  | SIConst id -> SIConst id
  | SIParam i -> assert_int @@ (!!) @@ List.nth params i
  | SIUnOp (op, se) -> SIUnOp (op, relocalize_fun (substitute_int var_env params) se)
  | SIBinOp (op, se1, se2) -> SIBinOp (op, relocalize_fun (substitute_int var_env params) se1, relocalize_fun (substitute_int var_env params) se2)
  | SIIf (c, se1, se2) -> SIIf (relocalize_fun (substitute_bool var_env params) c,
                                relocalize_fun (substitute_int var_env params) se1, relocalize_fun (substitute_int var_env params) se2)

and substitute_bool var_env params = function
  | SBool b -> SBool b
  | SBConst id -> SBConst id
  | SBParam i -> assert_bool @@ (!!) @@ List.nth params i
  | SBUnOp (op, se) -> SBUnOp (op, relocalize_fun (substitute_bool var_env params) se)
  | SBBinOp (op, se1, se2) -> SBBinOp (op, relocalize_fun (substitute_bool var_env params) se1, relocalize_fun (substitute_bool var_env params) se2)
  | SBBinIntOp (op, se1, se2) -> SBBinIntOp (op, relocalize_fun (substitute_int var_env params) se1, relocalize_fun (substitute_int var_env params) se2)
  | SBIf (c, se1, se2) -> SBIf (relocalize_fun (substitute_bool var_env params) c,
                                relocalize_fun (substitute_bool var_env params) se1, relocalize_fun (substitute_bool var_env params) se2)


let param var_env fname loc i = relocalize_fun @@ function
  | SOIntExp SUnknown uid -> SIntExp (assert_int @@ Misc.option_get ~error:(CouldNotInfer (fname, loc, i)) @@ find_opt uid var_env)
  | SOIntExp SExp se -> SIntExp se
  | SOBoolExp SUnknown uid -> SBoolExp (assert_bool @@ Misc.option_get ~error:(CouldNotInfer (fname, loc, i)) @@ find_opt uid var_env)
  | SOBoolExp SExp se -> SBoolExp se

let rec presize_to_size var_env = function
  | NetlistConstrainedAST.PSConst se ->
      Size !!se
  | NetlistConstrainedAST.PSVar   (id, i, uid) ->
      let se = assert_int @@ Misc.option_get ~error:(CouldNotSize (id, i)) @@ find_opt uid var_env in
      Size se
  | NetlistConstrainedAST.PSOtherContext (fname, loc, params, presize) ->
      let Size se = presize_to_size var_env presize in
      let params = List.mapi (param var_env fname loc) params in
      Size (substitute_int var_env params se)

let rec netlist_presize_to_netlist_size var_env = function
    | NetlistConstrainedAST.CDProd l -> TProd (List.map (netlist_presize_to_netlist_size var_env) l)
    | NetlistConstrainedAST.CDDim l ->  TDim  (List.map (presize_to_size var_env) l)

let resize_fun f var_env e =
  size (f !&!e) !&@e @@ netlist_presize_to_netlist_size var_env !&&e

let memparam var_env fname loc i = relocalize_fun @@ function
  | SUnknown uid -> (assert_int @@ Misc.option_get ~error:(CouldNotInfer (fname, loc, i)) @@ find_opt uid var_env)
  | SExp se -> se

let rec exp var_env e =
  let f = function
    | NetlistConstrainedAST.EConst c -> EConst c
    | NetlistConstrainedAST.EVar id -> EVar id
    | NetlistConstrainedAST.EReg e1 -> EReg (exp var_env e1)
    | NetlistConstrainedAST.ECall (fname, params, args) -> ECall (fname, List.mapi (param var_env !!fname !&@e) params, List.map (exp var_env) args)
    | NetlistConstrainedAST.EMem (mem_kind, (p1, p2, p3), args) ->
        let fname = match !!mem_kind with MRom -> "rom" | MRam -> "ram" in
        EMem (mem_kind, (memparam var_env fname !&@e 0 p1, memparam var_env fname !&@e 1 p2, p3), List.map (exp var_env) args)
  in
  resize_fun f var_env e

let rec lvalue var_env =
  let f = function
    | NetlistConstrainedAST.LValDrop -> LValDrop
    | NetlistConstrainedAST.LValId id -> LValId id
    | NetlistConstrainedAST.LValTuple l -> LValTuple (List.map (lvalue var_env) l)
  in
  resize_fun f var_env


let eqs _var_env _ (* NetlistConstrainedAST.{ equations; dim_env }*) = assert false (* TODO *)
  (* let sized_equations = List.map (fun NetlistConstrainedAST.{ desc = { eq_left; eq_right }; loc } ->
   *   relocalize loc { eq_left = lvalue var_env eq_left; eq_right = exp var_env eq_right }) equations in
   *
   * let size_env = Env.map (netlist_presize_to_netlist_size var_env) dim_env in
   * { equations = sized_equations; dim_env = size_env } *)



let body _var_env _e = assert false (* TODO *)
  (* relocalize_fun (function
   * | NetlistConstrainedAST.BIf (condition, block1, block2) -> BIf (condition, body var_env block1, body var_env block2)
   * | NetlistConstrainedAST.BEqs case -> BEqs (eqs var_env case)
   * ) e *)


let starput var_env NetlistConstrainedAST.{desc = { name; presize }; loc } =
  relocalize loc { name; size = relocalize_fun (netlist_presize_to_netlist_size var_env) presize }



let node var_env NetlistConstrainedAST.{ node_name_loc; node_loc; node_params; node_inline; node_inputs; node_outputs; node_body; node_probes } : node =
  let node_inputs  = List.map (starput var_env) node_inputs in
  let node_outputs = List.map (starput var_env) node_outputs in
  {
    node_inputs;
    node_outputs;
    node_body = body var_env node_body;
    node_name_loc; node_loc; node_inline; node_params; node_probes
  }

let program NetlistConstrainedAST.{ p_consts; p_consts_order; p_nodes; constraints } : program =
  try
    let var_env = Constraints_solver.solve_constraints constraints in
    {
      p_enum = [];
      p_consts; p_consts_order;
      p_nodes = Env.map (node var_env) p_nodes;
    }
  with
    | CouldNotSize (id, i) ->
        Format.eprintf "%aCould not size dimension %i of variable %s@." Location.print_location !@id i !!id; raise Errors.ErrorDetected
    | CouldNotInfer (fname, loc, i) ->
        Format.eprintf "%aCould not infer the value of parameter number %i of function %s@." Location.print_location loc i fname; raise Errors.ErrorDetected

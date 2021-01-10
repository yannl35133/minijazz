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
  | SIParam i -> assert_int @@ (!!) @@ List.nth params !**i
  | SIUnOp (op, se) -> SIUnOp (op, relocalize_fun (substitute_int var_env params) se)
  | SIBinOp (op, se1, se2) -> SIBinOp (op, relocalize_fun (substitute_int var_env params) se1, relocalize_fun (substitute_int var_env params) se2)
  | SIIf (c, se1, se2) -> SIIf (relocalize_fun (substitute_bool var_env params) c,
                                relocalize_fun (substitute_int var_env params) se1, relocalize_fun (substitute_int var_env params) se2)

and substitute_bool var_env params = function
  | SBool b -> SBool b
  | SBConst id -> SBConst id
  | SBParam i -> assert_bool @@ (!!) @@ List.nth params !**i
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
    | TProd l -> TProd (List.map (netlist_presize_to_netlist_size var_env) l)
    | TNDim l -> TNDim (List.map (presize_to_size var_env) l)

let global_presize_to_global_size var_env = function
  | BNetlist ti -> BNetlist (netlist_presize_to_netlist_size var_env ti)
  | BState s -> BState s
  | BStateTransition s -> BStateTransition s

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

let tritype_exp var_env = function
  | Exp e ->                Exp (exp var_env e)
  | StateExp e ->           StateExp e
  | StateTransitionExp e -> StateTransitionExp e

let rec lvalue var_env =
  let f = function
    | LValDrop -> LValDrop
    | LValId id -> LValId id
    | LValTuple l -> LValTuple (List.map (lvalue var_env) l)
  in
  (fun lval -> tritype (f !?!lval) !?@lval (global_presize_to_global_size var_env !??lval))


let rec decl var_env : NetlistConstrainedAST.decl -> decl =
  (relocalize_fun: 'a -> NetlistConstrainedAST.decl -> decl) @@ function
  | Deq (lval, e) ->
      Deq (lvalue var_env lval, tritype_exp var_env e)
  | Dlocaleq (lval, e) ->
      Dlocaleq (lvalue var_env lval, tritype_exp var_env e)
  | Dif (c, b1, b2) ->
      Dif (c, block var_env b1, block var_env b2)
  | Dreset (e, b) ->
      Dreset (exp var_env e, block var_env b)
  | Dmatch (e, m) ->
      Dmatch (e, matcher var_env m)
  | Dautomaton a ->
      Dautomaton (automaton var_env a)

and match_handler var_env ({ m_body; _} as handler) =
  { handler with m_body = block var_env m_body }

and matcher var_env ({ m_handlers; _} as matcher) =
  { matcher with m_handlers = ConstructEnv.map (match_handler var_env) m_handlers }

and transition var_env =
  List.map (fun (e1, e2) -> (exp var_env e1, e2))

and automaton_handler var_env ({ a_body; a_weak_transition; a_strong_transition; _ } as handler) =
  let a_body = block var_env a_body in
  let a_weak_transition   = transition var_env a_weak_transition in
  let a_strong_transition = transition var_env a_strong_transition in
  { handler with a_body; a_weak_transition; a_strong_transition}

and automaton fun_env ({ a_handlers; _} as auto) =
  { auto with a_handlers = ConstructEnv.map (automaton_handler fun_env) a_handlers }

and block var_env = List.map (decl var_env)


let starput var_env ({ ti_type; _ } as ti) =
  { ti with ti_type = relocalize_fun (global_presize_to_global_size var_env) ti_type }


let node var_env ({ node_inputs; node_outputs; node_body; node_variables; _ } as node) : node =
  let node_inputs  = List.map (starput var_env) node_inputs in
  let node_outputs = List.map (starput var_env) node_outputs in
  let node_variables = Env.map (fun ti -> { ti with b_type = global_presize_to_global_size var_env ti.b_type }) node_variables in
  { node with
    node_inputs;
    node_outputs;
    node_body = block var_env node_body;
    node_variables
  }

let program ({ p_nodes; _ } as program, constraints) : program =
  try
    let var_env = Constraints_solver.solve_constraints constraints in
    { program with
      p_nodes = FunEnv.map (node var_env) p_nodes;
    }
  with
    | CouldNotSize (id, i) ->
        Format.eprintf "%aCould not size dimension %i of variable %s@." Location.print_location !*@id i !*!id; raise Errors.ErrorDetected
    | CouldNotInfer (fname, loc, i) ->
        Format.eprintf "%aCould not infer the value of parameter number %i of function %s@." Location.print_location loc i fname; raise Errors.ErrorDetected

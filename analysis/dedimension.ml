open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let max_slice = ref (-1)
let add_one se1 = SIBinOp (SAdd, no_localize se1, no_localize (SInt 1))
let minus_one se1 = SIBinOp (SMinus, no_localize se1, no_localize (SInt 1))
let minus se1 se2 = SIBinOp (SMinus, no_localize se1, no_localize se2)
let mult se1 se2 = SIBinOp (SMult, no_localize se1, no_localize se2)
let map_mult = function
  | [] -> SInt 1
  | [se] -> se
  | hd :: tl -> List.fold_left mult hd tl

let rec dimension = function
  | TNDim [] -> TNDim []
  | TNDim l ->
      let l' = List.map (function Size n -> n) l in
      TNDim [Size (map_mult l')]
  | TProd p -> TProd ((List.map dimension) p)

let global_dim = function
  | BNetlist ti -> BNetlist (dimension ti)
  | t -> t

let rec value = function
  | VNDim (VNDim _ :: _ as l) ->
      value (VNDim (List.concat_map (function VNDim l -> l | _ -> assert false) l))
  | VNDim (VBit _ :: _) as v -> v
  | VNDim [] -> VNDim []
  | VBit b -> VBit b

let assert_int_param p = match !!p with
  | SIntExp e -> e
  | SBoolExp _ -> assert false

let rec split_n n = function
  | [] -> [], []
  | lst when n = 0 -> [], lst
  | hd :: tl -> let l1, l2 = split_n (n - 1) tl in hd :: l1, l2

let rec slice funname params args =
  let actions = List.tl @@ String.split_on_char '_' @@ Str.matched_group 1 !!funname in
  if List.length actions = 1 then ECall (funname, params, args) else begin
    let dims = List.length actions in
    max_slice := max !max_slice dims;
    let p = List.map assert_int_param params in
    let rec f actions dimparams params =
      match (actions, dimparams, params) with
      | "one" :: actions_tl, dim :: dimparams_tl, idx :: params_tl ->
          (dim, [idx; idx]) :: f actions_tl dimparams_tl params_tl
      | "all" :: actions_tl, dim :: dimparams_tl, params_tl ->
          (dim, [SInt 0; minus_one dim]) :: f actions_tl dimparams_tl params_tl
      | "from" :: actions_tl, dim :: dimparams_tl, from_arg :: params_tl ->
          (dim, [from_arg; minus_one dim]) :: f actions_tl dimparams_tl params_tl
      | "to" :: actions_tl, dim :: dimparams_tl, to_args :: params_tl ->
          (dim, [SInt 0; to_args]) :: f actions_tl dimparams_tl params_tl
      | "fromto" :: actions_tl, dim :: dimparams_tl, from_arg :: to_arg :: params_tl ->
          (dim, [from_arg; to_arg]) :: f actions_tl dimparams_tl params_tl
      | [], [], [] -> []
      | _ -> assert false
    in
    let dimparams, params = split_n dims p in
    let param_dims, param_actions = List.split @@ f actions dimparams params in
    let param_actions = List.concat param_actions in
    let params = List.map (fun e -> no_localize (SIntExp e)) (param_dims @ param_actions) in
    ECall (relocalize !@funname ("slice_flat_" ^ string_of_int dims), params, List.map exp args)
  end

and exp e =
  let regex = Str.regexp {|\(or\|and\|xor\|nand\|nor\|not\|mux\)_\([01]\)|} in
  let regex2 = Str.regexp {|add_dim_[0-9]+|} in
  let regex3 = Str.regexp {|concat_\([0-9]+\)|} in
  let regexp_slice = Str.regexp {|slice\(\(_\(all\|one\|to\|fromto\|from\)\)+\)|} in
  (fun e' -> size e' !$@e (dimension !$$e)) @@ match !$!e with
  | EConst v -> EConst (value v)
  | EVar id ->  EVar id
  | EReg e ->   EReg (exp e) (* Aux function for n_reg ? *)
  | ECall (funname, p, args) when Str.string_match regex !!funname 0 ->
      let op = Str.matched_group 1 !!funname in
      let dim = int_of_string @@ Str.matched_group 2 !!funname in
      if dim = 0 then
        ECall (relocalize !@funname @@ op ^ "_0", p, List.map exp args)
      else
        ECall (relocalize !@funname @@ op ^ "_1", [no_localize @@ SIntExp (map_mult @@ List.map assert_int_param p)], List.map exp args)

  | ECall (funname, _, [e]) when Str.string_match regex2 !!funname 0 ->
      !$!(exp e)
  | ECall (funname, p, args) when Str.string_match regex3 !!funname 0 ->
      let d = int_of_string (Str.matched_group 1 !!funname) in
      assert (d > 0);
      let p1, p2, tl = match p with
      | p1 :: p2 :: tl -> p1, p2, tl
      | _ -> assert false
      in
      let p1' = relocalize !@p1 @@ SIntExp (map_mult @@ List.map assert_int_param (p1 :: tl)) in
      let p2' = relocalize !@p2 @@ SIntExp (map_mult @@ List.map assert_int_param (p2 :: tl)) in
      ECall (relocalize !@funname "concat_1", [p1'; p2'], List.map exp args)

  | ECall (funname, p, args) when Str.string_match regexp_slice !!funname 0 ->
      slice funname p args

  | ECall (funname, p, args) -> ECall (funname, p, List.map exp args)
      (* function * params * args *)
  | EMem (m, static_args, args) -> EMem (m, static_args, List.map exp args)
      (* ro * (address size * word size * input file) * args *)


let tritype_exp = function
  | Exp e -> Exp (exp e)
  | StateExp e -> StateExp e
  | StateTransitionExp e -> StateTransitionExp e

let rec lvalue lval = (fun e -> tritype e !?@lval (global_dim !??lval)) @@ match !?!lval with
  | LValDrop -> LValDrop
  | LValId id -> LValId id
  | LValTuple l -> LValTuple (List.map lvalue l)

let rec decl d =
  relocalize !@d @@ match !!d with
  | Deq (lval, e) ->
     Deq (lvalue lval, tritype_exp e)
  | Dlocaleq (lval, e) ->
      Dlocaleq (lvalue lval, tritype_exp e)
  | Dif (c, b1, b2) ->
      Dif (c, block b1, block b2)
  | Dreset (e, b) ->
      Dreset (exp e, block b)
  | Dmatch (e, m) ->
      Dmatch (e, matcher m)
  | Dautomaton a ->
      Dautomaton (automaton a)


and match_handler ({ m_body; _} as handler) =
  { handler with m_body = block m_body }

and matcher ({ m_handlers; _} as matcher) =
  { matcher with m_handlers = ConstructEnv.map match_handler m_handlers }

and transition =
  List.map (fun (e1, e2) -> (exp e1, e2))

and automaton_handler ({ a_body; a_weak_transition; a_strong_transition; _ } as handler) =
  let a_body = block a_body in
  let a_weak_transition   = transition a_weak_transition in
  let a_strong_transition = transition a_strong_transition in
  { handler with a_body; a_weak_transition; a_strong_transition}

and automaton ({ a_handlers; _} as auto) =
  { auto with a_handlers = ConstructEnv.map automaton_handler a_handlers }

and block b = List.map decl b


let starput = List.map (fun ti -> { ti with ti_type = relocalize_fun global_dim ti.ti_type })

let slice_flat n : node FunEnv.t =
  let get_node n =
    let actions1 = String.concat ", " @@ List.init (n-1) (fun i -> Format.sprintf "from%i, to%i" (i+1) (i+1)) in
    let dims1 = List.init (n-1) (fun i -> Format.sprintf "dim%i" (i+1)) in
    let dims_params1 = String.concat ", " dims1 in
    let dims_mult = String.concat " * " dims1 in

    let node_params = Format.sprintf "dim0, %s, from0, to0, %s" dims_params1 actions1 in
    let min1_params = Format.sprintf "%s, %s" dims_params1 actions1 in
    let min1_name = Format.sprintf "slice_flat_%i" (n - 1) in
    let out_size = String.concat " * " @@ List.init n (fun i -> Format.sprintf "(to%i - from%i + 1)" i i) in
    let recall_params = Format.sprintf "dim0, %s, from0 + 1, to0, %s" dims_params1 actions1 in

    let slice_param = Format.sprintf "from0 * %s .. from0 * %s + %s - 1" dims_mult dims_mult dims_mult in
    if n = 2 then
      "slice_flat_2<dim0, dim1, from0, to0, from1, to1>(i:[dim0 * dim1]) = o:[(to0 - from0 + 1) * (to1 - from1 + 1)] where
          if from0 = to0 then
            o = i[from0 * dim1 + from1 .. from0 * dim1 + to1]
          else
            o = i[from0 * dim1 + from1 .. from0 * dim1 + to1] . slice_flat_2<dim0, dim1, from0+1, to0, from1, to1>(i)
          end if
        end where"
    else
      Format.sprintf "
        slice_flat_%i<%s>(i:[dim0 * %s]) = o:[%s] where
          if from0 = to0 then
            o = %s<%s>(i[%s])
          else
            o = %s<%s>(i[%s]) . slice_flat_%i<%s>(i)
          end if
        end where"
      n node_params dims_mult out_size min1_name min1_params slice_param min1_name min1_params slice_param n recall_params
  in
  let indices = if n > 1 then List.init (n-1) (fun i -> i + 2) else [] in
  let all_slice = List.map get_node indices in
  let program = String.concat "\n" all_slice in
  let lexbuf = Lexing.from_string program in

  (* Parsing of the file *)
  let parsing_ast = Parser.program Lexer.token lexbuf in

  let static_scoped_ast = Static_scoping.program parsing_ast in
  let static_typed_ast = Static_typer.program static_scoped_ast in
  let dimensioned_program = Netlist_dimensioning.program static_typed_ast in
  let constrained_program = Netlist_constrain.program dimensioned_program in

  let sized_program = Netlist_sizer.program constrained_program in
  sized_program.p_nodes



let node ({ node_inputs; node_outputs; node_body; _ } as node) =
  { node with node_inputs = starput node_inputs; node_outputs = starput node_outputs; node_body = block node_body }

let program ({ p_nodes; p_nodes_order; _ } as program) =
  let p_nodes0 = FunEnv.map node p_nodes in
  let p_nodes1 = slice_flat !max_slice in
  let p_nodes_order = p_nodes1
    |> FunEnv.to_seq
    |> List.of_seq
    |> List.map (fun (n, _) -> n)
    |> fun l -> l @ p_nodes_order
  in
  { program with p_nodes = FunEnv.union (fun _ a _ -> Some a) p_nodes0 p_nodes1; p_nodes_order }


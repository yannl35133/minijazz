open CommonAST
open StaticTypedPartialAST
open NetlistConstrainedAST

module UIDEnv = Map.Make(UniqueId)

type union_find =
  | LinkVar of (ident * int) * UniqueId.t
  | Direct of static_int_exp

type env = union_find UIDEnv.t

let rec mem uid env = match UIDEnv.find_opt uid env with
  | None -> false
  | Some Direct _ -> true
  | Some LinkVar (_, uid) -> mem uid env

let rec find uid env = match UIDEnv.find_opt uid env with
  | None -> invalid_arg "find"
  | Some Direct se -> se
  | Some LinkVar (_, uid) -> find uid env

let rec repr uid env = match UIDEnv.find_opt uid env with
  | None
  | Some Direct _ -> uid
  | Some LinkVar (_, uid) -> repr uid env

let add uid el env =
  let rep = repr uid env in
  assert (not (mem rep env));
  UIDEnv.add rep el env

let (&&) a b = match a, b with
  | Some false, _
  | _, Some false -> Some false
  | Some true, Some true -> Some true
  | _ -> None

let (||) a b = match a, b with
  | Some true, _
  | _, Some true -> Some true
  | Some false, Some false -> None
  | _ -> None

let rec static_equal = function
  | SInt n1,    SInt n2 -> Some (n1 = n2)
  | SIParam i1, SIParam i2 -> Some (i1 = i2)
  | SIConst v1, SIConst v2 -> Some (!!v1 = !!v2)
  | (SInt _ | SIParam _ | SIConst _), (SInt _ | SIParam _ | SIConst _) -> Some false   (* We don't want to rely on the equality of two value types *)
  | SIUnOp (SNeg, se1), SIUnOp (SNeg, se2) -> static_equal (!!se1, !!se2)
  | SIBinOp (op, se1, se2), SIBinOp (op', se1', se2') -> if op <> op' then None else static_equal (!!se1, !!se2) && static_equal (!!se1', !!se2')
  | SIIf (c, se1, se2), SIIf (c', se1', se2') -> if c <> c' then None else static_equal (!!se1, !!se2) && static_equal (!!se1', !!se2')
  | _ -> None

let analyze_result c1 c2 = function
  | Some true -> ()
  | None -> Format.eprintf "raise_warning c1 c2\n"
  | Some false -> failwith "raise_error"


let rec substitute_int params = function
  | SInt n -> SInt n
  | SIConst id -> SIConst id
  | SIParam i -> (let r = List.nth params i in match !!r with SOIntExp (SExp se) -> se | SOIntExp (SUnknown _) -> failwith "TODO" | SOBoolExp _ -> failwith "Static type error")
  | SIUnOp (op, se) -> SIUnOp (op, relocalize_fun (substitute_int params) se)
  | SIBinOp (op, se1, se2) -> SIBinOp (op, relocalize_fun (substitute_int params) se1, relocalize_fun (substitute_int params) se2)
  | SIIf (c, se1, se2) -> SIIf (relocalize_fun (substitute_bool params) c, relocalize_fun (substitute_int params) se1, relocalize_fun (substitute_int params) se2)

and substitute_bool params = function
  | SBool b -> SBool b
  | SBConst id -> SBConst id
  | SBParam i -> (let r = List.nth params i in match !!r with SOBoolExp (SExp se) -> se | SOBoolExp (SUnknown _) -> failwith "TODO" | SOIntExp _ -> failwith "Static type error")
  | SBUnOp (op, se) -> SBUnOp (op, relocalize_fun (substitute_bool params) se)
  | SBBinOp (op, se1, se2) -> SBBinOp (op, relocalize_fun (substitute_bool params) se1, relocalize_fun (substitute_bool params) se2)
  | SBBinIntOp (op, se1, se2) -> SBBinIntOp (op, relocalize_fun (substitute_int params) se1, relocalize_fun (substitute_int params) se2)
  | SBIf (c, se1, se2) -> SBIf (relocalize_fun (substitute_bool params) c, relocalize_fun (substitute_bool params) se1, relocalize_fun (substitute_bool params) se2)


 
let rec solve_constraint env = function
  | (PSOtherContext (_, _, params, PSConst se1) as c1), c2 ->
      solve_constraint env (PSConst (relocalize !@se1 (substitute_int params !!se1)), c2)
  | c1, (PSOtherContext (_, _, params, PSConst se2) as c2) ->
      solve_constraint env (c1, PSConst (relocalize !@se2 (substitute_int params !!se2)))
  | PSOtherContext (_, _, _, _), _ | _, PSOtherContext (_, _, _, _) ->
      env
  | PSVar (name, n, uid), PSVar (_, _, uid') when not @@ mem uid env ->
      add uid (LinkVar ((name, n), uid')) env
  | PSVar (_, _, uid'), PSVar (name, n, uid) when not @@ mem uid env ->
      add uid (LinkVar ((name, n), uid')) env
  | PSVar (_, _, uid), PSConst se when not @@ mem uid env ->
      add uid (Direct se) env
  | PSConst se, PSVar (_, _, uid) when not @@ mem uid env ->
      add uid (Direct se) env
  | (PSVar (_, _, uid) as c1), (PSVar (_, _, uid') as c2) ->
      let se = find uid env in
      let se' = find uid' env in
      analyze_result c1 c2 @@ static_equal (!!se, !!se');
      env
  | (PSVar (_, _, uid) as c1), (PSConst se' as c2) ->
      let se = find uid env in
      analyze_result c1 c2 @@ static_equal (!!se, !!se');
      env
  | (PSConst se as c1), (PSVar (_, _, uid') as c2) ->
      let se' = find uid' env in
      analyze_result c1 c2 @@ static_equal (!!se, !!se');
      env
  | (PSConst se as c1), (PSConst se' as c2) ->
      analyze_result c1 c2 @@ static_equal (!!se, !!se');
      env

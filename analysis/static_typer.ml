open Ast
module StaticScopedAST = Static_scoping.StaticScopedAST

module StaticTypedAST = struct
  type static_type =
    | TInt
    | TBool
  
  let static_type_to_string = function
    | TInt -> "int"
    | TBool -> "bool"
  
  let static_type_of_string id = relocalize !@id @@
    match !!id with
      | "int" -> TInt
      | "bool" -> TBool
      | _ -> raise @@ Errors.NotAType (!!id, !@id)

  type int_op = SAdd | SMinus | SMult | SDiv | SPower
  type int_bool_op = SEq | SNeq | SLt | SLeq | SGt | SGeq
  type bool_op = SOr | SAnd

  type int_unop = SNeg
  type bool_unop = SNot

  type static_int_exp_desc =
    | SInt    of int
    | SIParam of int
    | SIConst of ident
    | SIUnOp  of        int_unop * static_int_exp
    | SIBinOp of          int_op * static_int_exp * static_int_exp
    | SIIf    of static_bool_exp * static_int_exp * static_int_exp  (* se1 ? se2 : se3 *)

  and static_bool_exp_desc =
    | SBool   of bool
    | SBParam of int
    | SBConst of ident
    | SBUnOp  of       bool_unop * static_bool_exp
    | SBBinOp of         bool_op * static_bool_exp * static_bool_exp
    | SBBinIntOp of  int_bool_op * static_int_exp  * static_int_exp
    | SBIf    of static_bool_exp * static_bool_exp * static_bool_exp  (* se1 ? se2 : se3 *)

  and static_int_exp  = static_int_exp_desc  localized
  and static_bool_exp = static_bool_exp_desc localized

  type static_unknown_exp_desc =
    | SIntExp  of static_int_exp_desc  option
    | SBoolExp of static_bool_exp_desc option
  and static_unknown_exp = static_unknown_exp_desc localized

  type optional_static_int_exp_desc = static_int_exp_desc option
  and optional_static_int_exp = optional_static_int_exp_desc localized

  (* Netlist expressions *)

  type netlist_type =
    | TBitArray of optional_static_int_exp
    | TProd of netlist_type list


  type exp_desc =
    | EConst of ParsingAST.value
    | EVar   of ident
    | EReg   of exp
    | ECall  of ident * static_unknown_exp list * exp list
        (* function * params * args *)
    | EMem   of ParsingAST.mem_kind * (static_int_exp * static_int_exp * string option) * exp list
        (* ro * (address size * word size * input file) * args *)

  and exp = exp_desc localized

  type equation_desc = {
    eq_left:  ParsingAST.lvalue;
    eq_right: exp
  }
  and equation = equation_desc localized


  type typed_ident_desc = {
    name:  ident;
    typed: netlist_type localized;
  }
  and typed_ident = typed_ident_desc localized


  type block_desc =
    | BEqs of equation list
    | BIf  of static_bool_exp * block * block

  and block = block_desc localized

  type static_typed_ident_desc = {
    st_name: ident;
    st_type: static_type localized;
  }
  and static_typed_ident = static_typed_ident_desc localized

  type fun_env = static_type list Env.t

  type node = {
    node_name_loc:  Location.location;
    node_loc:       Location.location;
    node_params:    static_typed_ident list;
    node_inline:    ParsingAST.inline_status;
    node_inputs:    typed_ident list;
    node_outputs:   typed_ident list;
    node_body:      block;
    node_probes:    ident list;
  }

  type const = {
    const_decl:  static_unknown_exp;
    const_ident: Location.location;
    const_total: Location.location;
  }

  type program = {
    p_consts: const Env.t;
    p_consts_order: ident_desc list;
    p_nodes:  node  Env.t;
  }
end
open StaticTypedAST

let rec static_int_exp consts_env ?(params_env=IntEnv.empty) se =
  let fi = static_int_exp  consts_env ~params_env in
  let fb = static_bool_exp consts_env ~params_env in
  let static_int_unop sunop se1 = match sunop with
    | ParsingAST.SNeg -> SIUnOp (SNeg, fi se1)
    | ParsingAST.SNot -> raise Errors.TmpError
  in
  let static_int_binop sbinop se1 se2 = match sbinop with
    | ParsingAST.SAdd ->    SIBinOp (SAdd,   fi se1, fi se2)
    | ParsingAST.SMinus ->  SIBinOp (SMinus, fi se1, fi se2)
    | ParsingAST.SMult ->   SIBinOp (SMult,  fi se1, fi se2)
    | ParsingAST.SDiv ->    SIBinOp (SDiv,   fi se1, fi se2)
    | ParsingAST.SPower ->  SIBinOp (SPower, fi se1, fi se2)
    | SEq | SNeq | SLt | SLeq | SGt | SGeq | SOr | SAnd -> raise Errors.TmpError
  in

  try match !!se with
    | StaticScopedAST.SInt n ->
        relocalize !@se (SInt n)
    | StaticScopedAST.SBool _ ->
        raise Errors.TmpError
    | StaticScopedAST.SConst id -> begin
        match Env.find !!id consts_env with
          | TInt -> relocalize !@se (SIConst id)
          | TBool -> raise Errors.TmpError
        end
    | StaticScopedAST.SParam nb -> begin
      match IntEnv.find nb params_env with
        | TInt -> relocalize !@se (SIParam nb)
        | TBool -> raise Errors.TmpError
      end
    | StaticScopedAST.SUnOp (sunop, se1) ->
        relocalize !@se (static_int_unop sunop se1)
    | StaticScopedAST.SBinOp (sop, se1, se2) ->
        relocalize !@se (static_int_binop sop se1 se2)
    | StaticScopedAST.SIf (seb, se1, se2) ->
        relocalize !@se (SIIf (fb seb, fi se1, fi se2))
  with Errors.TmpError -> raise @@ Errors.WrongType ("bool", "int", !@se)


and static_bool_exp consts_env ?(params_env=IntEnv.empty) se =
  let fi = static_int_exp  consts_env ~params_env in
  let fb = static_bool_exp consts_env ~params_env in
  let static_bool_unop sunop se1 = match sunop with
    | ParsingAST.SNot -> SBUnOp (SNot, fb se1)
    | ParsingAST.SNeg -> raise Errors.TmpError
  in
  let static_bool_binop sbinop se1 se2 = match sbinop with
    | ParsingAST.SEq ->     SBBinIntOp (SEq,  fi se1, fi se2)
    | ParsingAST.SNeq ->    SBBinIntOp (SNeq, fi se1, fi se2)
    | ParsingAST.SLt ->     SBBinIntOp (SLt,  fi se1, fi se2)
    | ParsingAST.SLeq ->    SBBinIntOp (SLeq, fi se1, fi se2)
    | ParsingAST.SGt ->     SBBinIntOp (SGt,  fi se1, fi se2)
    | ParsingAST.SGeq ->    SBBinIntOp (SGeq, fi se1, fi se2)
    | ParsingAST.SOr ->     SBBinOp    (SOr,  fb se1, fb se2)
    | ParsingAST.SAnd ->    SBBinOp    (SAnd, fb se1, fb se2)
    | SAdd | SMinus | SMult | SDiv | SPower -> raise Errors.TmpError
  in

  try
    match !!se with
      | StaticScopedAST.SInt _ ->
          raise Errors.TmpError
      | StaticScopedAST.SBool b ->
          relocalize !@se (SBool b)
      | StaticScopedAST.SConst id -> begin
          match Env.find !!id consts_env with
            | TInt -> raise Errors.TmpError
            | TBool -> relocalize !@se (SBConst id)
          end
      | StaticScopedAST.SParam nb -> begin
        match IntEnv.find nb params_env with
          | TInt -> raise Errors.TmpError
          | TBool -> relocalize !@se (SBParam nb)
        end
      | StaticScopedAST.SUnOp (sunop, se1) ->
          relocalize !@se (static_bool_unop sunop se1)
      | StaticScopedAST.SBinOp (sop, se1, se2) ->
          relocalize !@se (static_bool_binop sop se1 se2)
      | StaticScopedAST.SIf (seb, se1, se2) ->
          relocalize !@se (SBIf (fb seb, fb se1, fb se2))
    with Errors.TmpError -> raise @@ Errors.WrongType ("int", "bool", !@se)

let static_unknown_exp consts_env ?(params_env=IntEnv.empty) se : static_unknown_exp =
  let int_exp = try Ok (static_int_exp consts_env ~params_env se)
    with Errors.WrongType arg -> Error (Errors.WrongType arg)
  in
  let bool_exp = try Ok (static_bool_exp consts_env ~params_env se)
    with Errors.WrongType arg -> Error (Errors.WrongType arg)
  in
  match int_exp, bool_exp with
    | Ok e, Error _ -> relocalize !@e (SIntExp (Some !!e))
    | Error _, Ok e -> relocalize !@e (SBoolExp (Some !!e))
    | Ok _, Ok _ ->       raise @@ Errors.NoTypes !@se
    | Error _, Error _ -> raise @@ Errors.TwoTypes !@se

let static_int_exp_full (consts_set, params_env) = static_int_exp consts_set ~params_env
let static_bool_exp_full (consts_set, params_env) = static_bool_exp consts_set ~params_env
let static_unknown_exp_full (consts_set, params_env) = static_unknown_exp consts_set ~params_env


let optional_static_unknown_exp env e = match !!e with
  | None -> relocalize !@e None
  | Some ed ->
      let res = static_unknown_exp_full env (relocalize !@e ed) in
      relocalize !@res (Some !!res)

let optional_static_int_exp env e : optional_static_int_exp = match !!e with
  | None -> relocalize !@e None
  | Some ed ->
      let res = static_int_exp_full env (relocalize !@e ed) in
      relocalize !@res (Some !!res)

let static_params types env params : static_unknown_exp list =
  let typed_params = List.map (optional_static_unknown_exp env) params in
  let static_param el ty = match !!el, ty with
    | Some SIntExp e1,  TInt ->  relocalize !@el (SIntExp e1)
    | Some SBoolExp e1, TBool -> relocalize !@el (SBoolExp e1)
    | None,             TInt ->  relocalize !@el (SIntExp None)
    | None,             TBool -> relocalize !@el (SBoolExp None)
    | Some SIntExp _,   TBool -> raise @@ Errors.WrongTypeParam (List.map static_type_to_string types, "int", "bool", !@el)
    | Some SBoolExp _,  TInt ->  raise @@ Errors.WrongTypeParam (List.map static_type_to_string types, "bool", "int", !@el)
  in
  List.map2 static_param typed_params types

let rec exp ((fun_env: fun_env), env) e = match !!e with
  | StaticScopedAST.EConst c ->
      relocalize !@e (EConst c)
  | StaticScopedAST.EVar id -> 
      relocalize !@e (EVar id)
  | StaticScopedAST.EReg e ->
      relocalize !@e (EReg (exp (fun_env, env) e))
  | StaticScopedAST.ECall (fname, params, args) ->
      let types = Env.find !!fname fun_env in
      relocalize !@e (ECall (fname, static_params types env params, List.map (exp (fun_env, env)) args))
  | StaticScopedAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
      let addr_size = static_int_exp_full env addr_size in
      let word_size = static_int_exp_full env word_size in
      relocalize !@e (EMem (mem_kind, (addr_size, word_size, input_file), List.map (exp (fun_env, env)) args))

let eq env = relocalize_fun @@ fun StaticScopedAST.{ eq_left; eq_right } ->
  { eq_left; eq_right = exp env eq_right }


let rec body (fun_env, env) e = relocalize_fun (function
  | StaticScopedAST.BIf (condition, block1, block2) -> BIf (static_bool_exp_full env condition, body (fun_env, env) block1, body (fun_env, env) block2)
  | StaticScopedAST.BEqs eq_l -> BEqs (List.map (eq (fun_env, env)) eq_l)
  ) e

let starput env = relocalize_fun @@ fun StaticScopedAST.{ name; typed } ->
  let rec fun_typed : StaticScopedAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_typed l)
    | TBitArray e -> TBitArray (optional_static_int_exp env e)
  in
  { name; typed = relocalize_fun fun_typed typed }


let params param_list : static_typed_ident list * static_type IntEnv.t =
  let new_params = List.map
    (fun (param: ParsingAST.static_typed_ident) ->
      relocalize !@param { st_name = !!param.st_name; st_type = static_type_of_string !!param.st_type_name }
    ) param_list in
  let param_env = Misc.fold_lefti (fun env i el -> IntEnv.add i !! (!!el.st_type) env) IntEnv.empty new_params in
  new_params, param_env

let fun_env StaticScopedAST.{ node_params; _ } =
  List.map (fun (param: ParsingAST.static_typed_ident) -> (!!) @@ static_type_of_string !!param.st_type_name) node_params

let node fun_env consts_env StaticScopedAST.{ node_name_loc; node_loc; node_params; node_inline; node_inputs; node_outputs; node_body; node_probes } : node =
  let new_params, params_env = params node_params in
  {
    node_params = new_params;
    node_inputs =   List.map (starput (consts_env, params_env)) node_inputs;
    node_outputs =  List.map (starput (consts_env, params_env)) node_outputs;
    node_body =     body (fun_env, (consts_env, params_env)) node_body;
    node_name_loc; node_loc; node_inline; node_probes
  }

let const consts_env StaticScopedAST.{ const_decl; const_ident; const_total } =
  {
    const_decl = static_unknown_exp consts_env const_decl;
    const_ident; const_total
  }

let program StaticScopedAST.{ p_consts; p_consts_order; p_nodes } : program =
  let type_const { const_decl; _ } = match !!const_decl with
    | SIntExp _ -> TInt
    | SBoolExp _ -> TBool
  in
  let consts_env = List.fold_left (fun consts_preenv el -> Env.add el (type_const @@ const consts_preenv @@ Env.find el p_consts) consts_preenv) Env.empty p_consts_order in
  let fun_env = Env.map fun_env p_nodes in
  { p_consts = Env.map (const consts_env) p_consts;
    p_consts_order;
    p_nodes = Env.map (node fun_env consts_env) p_nodes;
  }

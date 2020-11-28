open Ast
module StaticConstrainingAST = Static_constrain.StaticConstrainingAST
exception Scoping_error of string * Location.location

module StaticTypedAST = struct
  type sunop = ParsingAST.sunop
  type sop = ParsingAST.sop

  type static_exp_desc =
    | SInt   of int
    | SBool  of bool
    | SParam of int
    | SConst of ident
    | SUnOp  of      sunop * static_exp
    | SBinOp of        sop * static_exp * static_exp
    | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

  and static_exp = static_exp_desc static_typed

  and static_type =
    | TInt
    | TBool
  
  and 'a static_typed =
    {
      st_desc: 'a;
      st_loc: Location.location;
      st_type: static_type;
    }

  let (!$!) = fun obj -> obj.st_desc
  let (!$$) = fun obj -> obj.st_type
  let (!$@) = fun obj -> obj.st_loc

  let static_type desc loc typ = {
    st_desc = desc;
    st_type = typ;
    st_loc = loc
  }
  
  let static_type_same { desc; loc } typ = static_type desc loc typ


  type optional_static_exp_desc = static_exp_desc option
  and optional_static_exp = optional_static_exp_desc static_typed

  (* Netlist expressions *)

  type netlist_type =
    | TBitArray of optional_static_exp
    | TProd of netlist_type list


  type exp_desc =
    | EConst of ParsingAST.value
    | EVar   of ident
    | EReg   of exp
    | ECall  of ident * optional_static_exp list * exp list
        (* function * params * args *)
    | EMem   of ParsingAST.mem_kind * (static_exp * static_exp * string option) * exp list
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
    | BIf  of static_exp * block * block

  and block = block_desc localized

  type param = {
    st_type: static_type;
    st_name: ident_desc;
    st_loc:  Location.location;
  }

  type node = {
    node_name_loc:  Location.location;
    node_loc:       Location.location;
    node_params:    param list;
    node_inline:    ParsingAST.inline_status;
    node_inputs:    typed_ident list;
    node_outputs:   typed_ident list;
    node_body:      block;
    node_probes:    ident list;
  }

  type const = {
    const_decl:   static_exp;
    const_idents: Location.location;
    const_totals: Location.location;
  }

  type program = {
    p_consts: const Env.t;
    p_nodes:  node  Env.t;
  }

  (* TODO: Revoir variables environment *)
  type varenv = static_exp_desc static_typed list Env.t
end
open StaticTypedAST

let fulfill_constraints (consts, params) = function
  | [] -> None
  | StaticConstrainingAST.CParam nb :: tl -> Some (List.nth n params).st_type
  | StaticConstrainingAST.CConstant id :: tl -> Some !$$(Env.find !!id consts)
  | StaticConstrainingAST.CUnoparg of  sunop
  | StaticConstrainingAST.CUnopres of  sunop
  | StaticConstrainingAST.CBinoparg of sop
  | StaticConstrainingAST.CBinopres of sop
  | StaticConstrainingAST.CCondition
  | StaticConstrainingAST.CThenElse of static_exp

let rec constrain_static_exp ?constraints:(acc=([] : static_type_constraints list)) (st_exp: PreTypingAST.static_exp):
  static_exp_desc static_typed =

  match !!st_exp with
    | SInt n ->
        static_constrain (SInt n) !@st_exp acc
    | SBool b ->
        static_constrain (SBool b) !@st_exp acc
    | SIdent id ->
        static_constrain (SIdent id) !@st_exp (CConstant id :: acc)
    | SUnOp (unop, e) ->
        let constrained = constrain_static_exp e ~constraints:[CUnoparg unop] in
        static_constrain (SUnOp (unop, constrained)) !@st_exp (CUnopres unop :: acc)
    | SBinOp (op, e1, e2) ->
        let constrained1 = constrain_static_exp e1 ~constraints:[CBinoparg op] in
        let constrained2 = constrain_static_exp e2 ~constraints:[CBinoparg op] in
        static_constrain (SBinOp (op, constrained1, constrained2)) !@st_exp (CBinopres op :: acc)
    | SIf (eb, e1, e2) ->
        let constrainedb = constrain_static_exp eb ~constraints:[CCondition] in
        let constrained1 = constrain_static_exp e1 ~constraints:[] in
        let constrained2 = constrain_static_exp e2 ~constraints:[CThenElse constrained1] in
        static_constrain (SIf (constrainedb, constrained1, constrained2)) !@st_exp (CThenElse constrained1 :: acc)



let constrain_optional_static_exp e = match !!e with
  | None -> static_constrain None !@e []
  | Some ed ->
      let res = constrain_static_exp (relocalize !@e ed) in
      { res with st_desc = Some !$!res }


let rec constrain_exp e = match !!e with
  | PreTypingAST.EConst c ->  relocalize !@e (EConst c)
  | PreTypingAST.EVar id ->   relocalize !@e (EVar id)
  | PreTypingAST.EReg e ->    relocalize !@e (EReg (constrain_exp e))
  | PreTypingAST.ECall (fname, params, args) ->
                            relocalize !@e (ECall (fname, List.map constrain_optional_static_exp params, List.map constrain_exp args))
  | PreTypingAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
                            relocalize !@e (EMem (mem_kind, (constrain_static_exp addr_size, constrain_static_exp word_size, input_file),
                                                  List.map constrain_exp args))

let constrain_eq = relocalize_fun (fun PreTypingAST.{ eq_left; eq_right } ->
  { eq_left; eq_right = constrain_exp eq_right }
)

let rec constrain_body e = relocalize_fun (function
  | PreTypingAST.BIf (condition, block1, block2) -> BIf (constrain_static_exp condition, constrain_body block1, constrain_body block2)
  | PreTypingAST.BEqs eq_l -> BEqs (List.map constrain_eq eq_l)
  ) e

let constrain_starput = relocalize_fun (fun PreTypingAST.{ name; typed } ->
  let rec constrain_typed : PreTypingAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map constrain_typed l)
    | TBitArray e -> TBitArray (constrain_optional_static_exp e)
  in
  { name; typed = relocalize_fun constrain_typed typed }
)

let constrain_node PreTypingAST.{ node_name_loc; node_loc; node_inline; node_inputs; node_outputs; node_params; node_body; node_probes } =
  {
    node_inputs =   List.map constrain_starput node_inputs;
    node_outputs =  List.map constrain_starput node_outputs;
    node_body =     constrain_body node_body;
    node_name_loc; node_loc; node_inline; node_params; node_probes
  }

let constrain_const PreTypingAST.{ const_decl; const_idents; const_totals } =
  {
    const_decl = constrain_static_exp const_decl;
    const_idents; const_totals
  }

let program PreTypingAST.{ p_consts; p_nodes } : program =
  {
    p_consts = Env.map constrain_const p_consts;
    p_nodes = Env.map constrain_node p_nodes;
  }






(* Entry point *)
let type_program ParsingAST.{ p_consts; p_nodes } =

  let empty_consts = {
    const_values = Env.empty;
    const_idents = Env.empty;
    const_decls  = Env.empty
  } in

  (* 1: type constant declarations *)
  let typed_consts = type_consts empty_consts p_consts in

  let fun_env = analyse p_nodes in


  let typed_nodes = type_nodes typed_consts p_nodes in
  typed_consts, typed_nodes
  (* let translate_vars types stru =
    let vars = snd !$stru in
    List.map (fun (name, typ) -> !$name, check_type types typ) vars
  in
  let structs_attrs = List.fold_left (fun map stru -> Smap.add ("!" ^ !$(fst !$stru)) (translate_vars types stru) map) Smap.empty structs in

  (* 2a: check types of parameters *)
  let func_env =
    let one_func_env funcs_env0 ((name, vars, _, _): Parse.func) =
      let locals_refd = List.fold_left (add_var types) empty_locals vars in
      add_funcs_env funcs_env0 name locals_refd
    in
    List.fold_left one_func_env Smap.empty funcs
  in

  let func_types =
    let one_func_type (env: func_types) ((name, vars, return_type0, _): Parse.func): func_types =
      let args_type0 = Prod (List.map (fun (_name, typ) -> typ) vars) in
      let args_type   = check_type types args_type0
      and return_type = check_type types return_type0 in
      Smap.add !$name (args_type, return_type) env
    in
    List.fold_left one_func_type Smap.empty funcs
  in
  if not (Smap.mem "main" func_types) then
    raise (NameError (def_lst.loc, "Function main is undeclared"))
  else if Smap.find "main" func_types <> (Prod [], Prod []) then
    raise (NameError (def_lst.loc, "Function main should take no arguments and return nothing"));

  (* 3a *)
  let tfuncs: func list = List.map (tfunc (types, structs_env, func_types) func_env) funcs in

  if !fmt = -1 then
    raise (VariableNotUsed (fmt_import.loc, "Module \"fmt\" imported but not used"));

  (func_types, structs_attrs), tfuncs *)



let tfunc (types, structs_env, func_types) funcs_env (name, vars, _, block) =
  let locals = Smap.find !$name funcs_env in
  let return_type = snd (Smap.find !$name func_types) in

  let locals1, tblock, returns = tblock (types, structs_env, func_types, return_type) locals block in
  let refd = snd locals1 in

  if not returns && return_type <> Prod [] then
    raise (TypeError (block.loc, "Reached the end of function without finding return"));

  !$name, translate_vars types refd vars, return_type, tblock


and tblock (globals: globals) (locals0, refd0) block =
  let rec fold_map (locals0: locals) = function
    | hd :: tl -> let locals1, tstmt, returns2 = tstmt globals locals0 hd in
                  let locals2, other_tstmts, returns = fold_map locals1 tl in
                  locals2, tstmt :: other_tstmts, returns || returns2
    | []       -> locals0, [], false
  in
  let locals1, stmts, returns = fold_map ((Smap.empty, Smap.empty) :: locals0, refd0) !$block in
  let (used, refd1, tail) = match locals1 with
    | (_, used) :: tail, refd -> (used, refd, tail)
    | [], _                   -> failwith "Empty environment"
  in
  if not (Smap.for_all (fun _key b -> b) used) then
    let pb_var = fst (Smap.choose (Smap.filter (fun _key b -> not b) used)) in
    raise (VariableNotUsed (block.loc, "Variable " ^ pb_var ^ " defined but not used"))
  else
    let tblock = package_block stmts refd1 in
    (tail, refd1), tblock, returns



and tstmt   globals           locals0 stmt                                   = match !$stmt with
  | Sempty                         -> locals0, Sempty, false
  | Seval e                        -> let locals, te = (texpr  globals locals0 e) in locals, Seval te, false
  | Spp e                     -> (try let locals, te = (tlexpr globals locals0 e) in locals, Spp   te, false
                                  with NotALValue loc -> raise (SyntaxError (loc, "Cannot assign to this value; expected name, attribute or indirection")))
  | Smm e                     -> (try let locals, te = (tlexpr globals locals0 e) in locals, Smm   te, false
                                  with NotALValue loc -> raise (SyntaxError (loc, "Cannot assign to this value; expected name, attribute or indirection")))

  | Sassign (l1, l2)               -> assign globals locals0 (l1, l2)

  | Sblock b                       -> let locals, tblock, returns = tblock globals locals0 b in
                                      locals, Sblock tblock, returns

  | Sif (e, b1, b2)                -> let locals, te = texpr globals locals0 e in
                                      let locals1, tblock1, returns1 = tblock globals locals  b1 in
                                      let locals2, tblock2, returns2 = tblock globals locals1 b2 in
                                      if te.typ = Prim "bool" then
                                        locals2, Sif (te, tblock1, tblock2), returns1 && returns2
                                      else raise (TypeError (e.loc, "This expression has type " ^ typ_to_string te.typ ^ " but an expression was expected of type bool, as the condition of an if-statement"))

  | Sdecl (l1, typ, l2)            -> decl globals locals0 (l1, typ, l2) stmt.loc

  | Sreturn l                      -> return globals locals0 l


  | Sfor (e, b)                    -> let locals, te = texpr globals locals0 e in
                                      let locals1, tblock, _returns = tblock globals locals b in

                                      if te.typ = Prim "bool" then
                                        locals1, Sfor (te, tblock), false
                                      else raise (TypeError (e.loc, "This expression has type " ^ typ_to_string te.typ ^ " but an expression was expected of type bool, as the condition of a for loop"))



and texpr   globals           locals0 ?(add_refd=false)  expr: locals * expr = match !$expr with
  | Cnil           -> locals0, package (Cnil)      (VoidPoint)
  | Cbool b        -> locals0, package (Cbool b)   (Prim "bool")
  | Cint n         -> locals0, package (Cint n)    (Prim "int")
  | Cstring s      -> locals0, package (Cstring s) (Prim "string")
  | Cempty         -> failwith "We were not supposed to go this far!"
  | Eident id      -> let locals, typ = find_var globals locals0 ~add_refd id in
                        locals, package (Eident !$id) typ
  | Eattr (e, id)  -> let locals, te =  texpr globals locals0 e in
                      let locals2, tte = attr globals locals te id e.loc in
                        locals2, tte
  | Ecall (id, l)  -> call globals locals0 id l
  | Eprint l       -> if mem_var locals0 "fmt" then raise (TypeError (expr.loc, "The expression 'fmt' has no method 'Print'"))
                      else if !fmt = 0 then raise (NameError (expr.loc, "Name fmt is not defined"))
                      else fmt := 1;
                      let locals, tl, _ = fold_map_args texpr globals locals0 l in
                        locals, package (Eprint tl) (Prod [])

  | Eunop (Uneg, e)  -> let locals, te = texpr globals locals0 e in
                        match_typ (Prim "int")  te.typ e.loc;
                          locals, package (Eunop (Uneg, te)) (Prim "int")
  | Eunop (Unot, e)  -> let locals, te = texpr globals locals0 e in
                        match_typ (Prim "bool") te.typ e.loc;
                          locals, package (Eunop (Unot, te)) (Prim "bool")

  | Eunop (Uref, e)  -> let locals, te = try tlexpr globals locals0 ~add_refd: true e
                        with NotALValue loc -> raise (SyntaxError (loc, "Cannot take the reference of such a value; expected name, attribute or indirection")) in
                          locals, package (Eref te) (Point te.typ)
  | Eunop (Uind, e)  -> let locals, te = texpr globals locals0 e in begin
                          match te.typ with
                            | Point t         -> locals, package (Eind te) t
                            | VoidPoint       -> raise (TypeError (e.loc, "Cannot dereference a nil pointer"))
                            | Prod [Point _t] -> failwith "Why is there only one type?"
                            | Prod []         -> raise (TypeError (e.loc, "Expression does not have a type"))
                            | Prim _ | Prod _ -> raise (TypeError (e.loc, "Cannot dereference an element of type " ^ typ_to_string te.typ))
                          end

  | Ebinop (op, e1, e2) -> binop globals locals0 expr.loc (op, e1, e2)

and tlexpr  globals           locals  ?(add_refd=false) (expr: Parse.expr)   = match !$expr with
  | Eident id             -> if !$id = "_" then
                             raise (NameError (expr.loc, "_ cannot be used as a value"))
                             else texpr globals locals ~add_refd expr
  | Eattr _  | Eunop (Uind, _) -> texpr globals locals ~add_refd expr
  |Eunop ((Uneg|Unot|Uref), _)|Cempty|Cnil|Cbool _|Cstring _|Cint _|Ecall (_, _)|Eprint _|Ebinop (_, _, _)-> raise (NotALValue expr.loc)








(* debug functions *)
let print_set s =
  Sset.iter (fun x -> print_endline x) s
let print_map m =
  Smap.iter (fun x _ -> print_endline x) m

let empty_locals = [Smap.empty, Smap.empty], Smap.empty

let ordinal n =
  string_of_int n ^
  match n mod 10 with
    | 1 -> "st"
    | 2 -> "nd"
    | 3 -> "rd"
    | _ -> "th"

let fmt = ref 0   (* 0: not imported; -1: imported; 1: imported and used *)

let rec separate : Parse.def list -> 'a = function
  | [] -> [], []
  | Function  f :: tl -> let l1, l2 = separate tl in l1, f :: l2
  | Structure s :: tl -> let l1, l2 = separate tl in s :: l1, l2

and add_type     (types: typs) (stru: Parse.stru) : typs =
  let typ = fst !$stru in
  if !$typ = "_" then types else
  let new_name = "!" ^ !$typ in
  if Sset.mem new_name types then
    raise (NameAlreadyTaken (typ.loc, ("Name " ^ !$typ ^ " is already defined")))
  else
    Sset.add new_name types

and check_type   (types: typs) = function
  | Point typ -> Point (check_type types typ)
  | Prim  id  -> if id = "_" then raise (MissingLoc ("Type _ cannot be used as a value"))
            else if Sset.mem ("!" ^ id) types then Prim ("!" ^ id)   (* Struct types *)
            else if Sset.mem id         types then Prim id           (* Native types *)
            else raise (MissingLoc ("Type " ^ id ^ " is undefined"))
  | Prod  p   -> Prod (List.map (check_type types) p)
  | VoidPoint -> failwith "How did nil get here?"


and add_var  types ((locals, refd): locals) (name, typ) =
  let new_type =
    try check_type types typ
    with MissingLoc s -> raise (TypeError (name.loc, s))
  in
  let env, used, tail = match locals with
    | []                  -> failwith "Empty environment"
    | (env, used) :: tail -> env, used, tail
  in
  if !$name = "_" then
    locals, refd
  else if Smap.mem !$name env then
    raise (NameAlreadyTaken (name.loc, ("Name " ^ !$name ^ " is already defined")))
  else
    (Smap.add !$name new_type env,
     Smap.add !$name false used) :: tail,
     Smap.add !$name false refd

and add_attr types struct_env               (name, typ) =
  let locals, _refd = add_var types ([struct_env, Smap.empty], Smap.empty) (name, typ) in
  let env = match locals with
    | (env, _used) :: _tail -> env
    | []                    -> failwith "Empty environment"
  in
  env

and add_structs_env (structs_env: structs_env) name env =
  if !$name = "_" then structs_env else
  let new_name = "!" ^ !$name in
  if Smap.mem new_name structs_env then
    raise (NameAlreadyTaken (name.loc, ("Name " ^ !$name ^ " is already defined")))
  else
    Smap.add new_name env structs_env

and add_funcs_env   (funcs_env: funcs_env)     name env =
  if !$name = "_" then funcs_env else
  if Smap.mem !$name funcs_env then
    raise (NameAlreadyTaken (name.loc, ("Name " ^ !$name ^ " is already defined")))
  else
    Smap.add !$name env funcs_env

and check_deps types (s_lst : Parse.stru list): structs_env =
  let structs_env_ref = ref Smap.empty in

  let arr =        Array.of_list s_lst in
  let names =      Array.map (fun stru -> fst !$stru) arr in
  let attributes = Array.map (fun stru -> snd !$stru) arr in

  let n = Array.length arr in

  let index = ref Smap.empty in  (* Struct name -> place in adj. matrix *)
  for i = 0 to n-1 do
    index := Smap.add ("!" ^ !$(names.(i))) i !index
  done;

  let adj = Array.make_matrix n n false in


  let check_one_type index_struct struct_env (var: Parse.var) =
    let name, typ = var in
    begin match typ with
      | Point _typ  -> ()
      | Prim id     -> begin  try adj.(index_struct).(Smap.find ("!" ^ id) !index) <- true
                              with Not_found -> () end
      | VoidPoint   -> failwith "How did nil get here?"
      | Prod _      -> failwith "Why is there a function call?"
    end;
    (* Here, check that attribute names are unique and types well-formed *)
    add_attr types struct_env (name, typ)
  in

  for i = 0 to n-1 do
    let struct_env = List.fold_left (check_one_type i) Smap.empty attributes.(i) in

    structs_env_ref := add_structs_env !structs_env_ref names.(i) struct_env
  done;


  let visit = Array.make n 0 in
  let rec dfs i =
    if visit.(i) = 2 then
      raise (TypeError (arr.(i).loc, "Circular definition in type " ^ !$(names.(i)) ));
    if visit.(i) = 0 then
      visit.(i) <- 2;
      for j = 0 to n-1 do
        if adj.(i).(j) then
          dfs j
      done;
      visit.(i) <- 1
  in
  for i = 0 to n-1 do dfs i done;
  !structs_env_ref



and translate_vars types refd vars =
    List.map (fun (name, typ) -> !$name, check_type types typ, !$name <> "_" && Smap.find !$name refd) vars

and expr_to_type  (types: typs) (expr: Parse.expr) = match !$expr with
  | Eident id -> begin try check_type types (Prim !$id)
                  with MissingLoc _ -> raise (NameError (expr.loc, "The name " ^ !$id ^ " does not refer to a valid type")) end
  | Eunop (Uind, e)                             -> Point (expr_to_type types e)
  | Eunop ((Uneg|Unot|Uref), _)|Cempty|Cnil|Cbool _|Cstring _|Cint _|Eattr (_, _)|Ecall (_, _)|Eprint _|Ebinop (_, _, _)
                                                -> raise (SyntaxError (expr.loc, "The argument of function new must be a valid type"))

and mem_var   (locals: locals) (name: string)      = match locals, name with
  | _, "_"         -> false
  | ([], _refd), _ -> false
  | ((env, _used) :: _tail, _refd), s when (Smap.mem s env) -> true
  | (_locals :: tail, refd), _     -> mem_var (tail, refd) name

and find_var  ((_, strus, funcs, _) as globals: globals) (locals: locals) ?(add_refd=false) (id: Parse.ident): locals * typ = match locals, !$id with
  | _,                   "_" -> raise (NameError (id.loc, "Name _ cannot be used as a value"))
  | ((env, used) :: tail, refd), s when (Smap.mem s env) ->
                              let new_refd = match add_refd, Smap.find !$id env with
                                | _, Prim typ when Smap.mem typ strus -> refd
                                | true, _                             -> Smap.add !$id true refd
                                | false, _                            -> refd
                              in
                                ((env, Smap.add !$id true used) :: tail, new_refd), Smap.find !$id env
  | (locals      :: tail, refd), _s  ->
                              let (nonlocals, refd), res = find_var globals (tail, refd) ~add_refd id in
                                (locals :: nonlocals, refd), res
  | ([], _), s  when (Smap.mem s funcs) ->
                                raise (NameError (id.loc, !$id ^ " is a function and cannot be used as a value"))
  | ([], _), s  when (Smap.mem ("!" ^ s) strus) ->
                                raise (NameError (id.loc, !$id ^ " is a struct type and cannot be used as a value"))
  | ([], _), _s              -> raise (NameError (id.loc, "Variable name " ^ !$id ^ " is not defined"))

and match_typ ideal_type other_type loc =
  let rec catch_prods n t1 t2 = match t1, t2 with
    | Prod [],           Prod []               -> ()
    | Prod (hd1 :: tl1), Prod (hd2 :: tl2)     -> (inner n hd1 hd2; catch_prods (n+1) (Prod tl1) (Prod tl2))
    | Prod lst1,         Prod lst2             -> let l1 = List.length lst1 and l2 = List.length lst2 in
                                                    raise (AssMism0 (n - 1 + l1, n - 1 + l2))

    | Prod _,            _                     -> failwith "Comparing apples to oranges, huh?!"
    | _,                 Prod _                -> raise (MissingLoc_n (-1, "Cannot use a multi-valued function with other values"))

    | ((VoidPoint | Prim _ | Point _), (VoidPoint | Prim _ | Point _)) -> inner (-1) t1 t2

  and inner n t1 t2 = match t1, t2 with
    | Prim  id1,  Prim  id2
             when id1 = id2   -> ()
    | Point _typ, VoidPoint   -> ()
    | Point typ1, Point typ2  -> inner n typ1 typ2
    | Prim  _id1, Prim  _id2  -> raise (TypeMismatch n)
    | Point _,    Prim  _     -> raise (TypeMismatch n)
    | Prim  _,    Point _     -> raise (TypeMismatch n)
    | Prim  _,    VoidPoint   -> raise (TypeMismatch n)
    | Prod  _,    Prod  _     -> failwith "Using two levels of functions, or what?!"
    | Prod  _,    _           -> failwith "Comparing apples to oranges, huh?!"
    | _,          Prod  _     -> raise (MissingLoc_n (n, "Cannot use a multi-valued function with other values"))
    | VoidPoint,  _           -> failwith "How did nil get here?"
  in

  try catch_prods 1 ideal_type other_type
  with
    | TypeMismatch -1 -> raise (TypeError (loc, "This expression of type " ^ typ_to_string other_type ^ " is supposed to have type " ^ typ_to_string ideal_type))
    | MissingLoc_n (-1, s) -> raise (TypeError (loc, s))
  (*| TypeMismatch n  -> Caught directly in call, return, assign or decl2 *)

and attr      ((_, structs_env, _, _)         : globals) locals  te (id: Parse.ident) loc: locals * expr =
  let find_typ typ_name =
    if typ_name = "_" then raise (MissingLoc ("Type _ cannot be used as a value")) else
    if not (Smap.mem typ_name structs_env) then
      raise (TypeError (loc, "This expression of type " ^ typ_name ^ " does not have attributes"))
    else
      let stru = Smap.find typ_name structs_env in
      if !$id = "_" then raise (NameError (id.loc, "Attribute name _ cannot be used as a value")) else
      if not (Smap.mem !$id stru) then
        raise (NameError (id.loc, "Attribute name " ^ !$id ^ " is not defined for type " ^ typ_name))
      else
        Smap.find !$id stru
  in

  match te.typ with
    | Prim typ_name ->
        let typ = find_typ typ_name in
        locals, package (Eattr (te, !$id)) typ

    | Point (Prim typ_name) ->
        let typ = find_typ typ_name in
        locals, package (Eattr (package (Eind te) (Prim typ_name), !$id)) typ

    | Prod [_t] -> failwith "Why is there a single type?"
    | Prod  _   -> raise (TypeError (loc, "This expression of type " ^ typ_to_string te.typ ^ " cannot possibly have attributes"))
    | VoidPoint -> raise (TypeError (loc, "Cannot dereference a nil pointer"))
    | Point _   -> raise (NameError (loc, "This expression is a pointer pointer and does not have attributes"))



and fold_map_args (func: expr_typer)            globals           locals = function
  | hd :: tl -> let locals1, te = func globals locals hd in
                let locals2, tl, types = fold_map_args func globals locals1 tl in
                  locals2, te :: tl, te.typ :: types
  | []       ->   locals, [], []


and call ((types, _, func_types, _) as globals: globals) locals0 (id: Parse.ident)  (l:  Parse.params) =
  if !$id = "new" && not (Smap.mem !$id func_types) then
    let arg0 = match !$l with
      | [el] -> el
      | [] | _ :: _ :: _ -> raise (NameError (l.loc, string_of_int (List.length !$l) ^ "values passed instead of 1"))
    in
    let arg = expr_to_type types arg0 in
    locals0, package NewStru (Point arg)
  else if !$id = "_" then raise (MissingLoc ("Function _ cannot be used as a value")) else
  if not (Smap.mem !$id func_types) then
    raise (NameError (id.loc, "The name " ^ !$id ^ " is not that of a function"))
  else
  let args_types0, return_types = Smap.find !$id func_types in
  let args_types = match args_types0 with
    | Prod r_typs -> r_typs
    | _           -> failwith "How did we come here?"
  in
  let return_mode = match return_types with
    | Prim _
    | Point _   -> true
    | Prod _    -> false
    | VoidPoint -> failwith "How did nil get here?"
  in
  let locals, tl, types0 = fold_map_args texpr globals locals0 !$l in
  let types, texpr, fcall = match types0, tl with
    | [Prod []],                   [{desc = (Ecall_l (id, _, _) | Ecall_f (id, _, _, _)); typ=_}]       -> raise (SyntaxError (l.loc, "Cannot use the call to " ^ id ^ " as a value"))
    | [Prod (_ :: _ :: _ as lst)], [{desc = (Ecall_l _          | Ecall_f _            ); typ=_} as el] -> lst, Ecall_f (!$id, return_mode, List.length lst, el),   true
    | lst,        lst2                                                                                  -> lst, Ecall_l (!$id, return_mode, lst2), false
  in
  begin try match_typ args_types0 (Prod types) l.loc
  with
    | TypeMismatch  n        -> let supposed_type = List.nth args_types (pred n)
                                and pb_type = if fcall then (List.hd tl).typ else (List.nth tl  (pred n)).typ
                                and pb_loc  = if fcall then l.loc            else (List.nth !$l (pred n)).loc in
        raise (TypeError (pb_loc, "This expression of type " ^ typ_to_string pb_type ^ " is supposed to have type " ^ typ_to_string supposed_type ^ " as " ^ ordinal n ^ " argument of " ^ !$id))
    | AssMism0     (n1, n2)  -> raise (AssignmentMismatch (l.loc, string_of_int n2 ^ " values passed instead of " ^ string_of_int n1 ^ "\nType wanted: (" ^ typ_to_string args_types0 ^ "); type received: (" ^ typ_to_string (Prod types) ^ ")"))
    | MissingLoc_n (n, s)    -> let loc = if fcall then l.loc else (List.nth !$l (pred n)).loc in
                                raise (TypeError (loc, s))
  end;
  locals, package texpr return_types


and return ((_, _, _, return_type0) as globals: globals) locals0                    (l:  Parse.params) =
  let return_type = match return_type0 with
    | Prod r_typs -> r_typs
    | single_type -> [single_type]
  in

  let locals, tl, types0 = fold_map_args texpr globals locals0 !$l in
  let types, stmt, fcall = match types0, tl with
  | [Prod []],    [{desc = (Ecall_l (id, _, _) | Ecall_f (id, _, _, _)); typ=_}]       -> raise (SyntaxError (l.loc, "Cannot use the call to " ^ id ^ " as a value"))
  | [Prod [typ]], [el]                                                                 -> [typ], Sreturn1 el,   true
  | [Prod lst],   [{desc = (Ecall_l _          | Ecall_f _            ); typ=_} as el] -> lst,   Sreturnf el,   true
  | [typ],        [el]                                                                 -> [typ], Sreturn1 el,   false
  | lst,          lst2                                                                 -> lst,   Sreturnm lst2, false
  in
  begin try match_typ (Prod return_type) (Prod types) l.loc
  with
    | TypeMismatch n         -> let supposed_type = List.nth return_type (pred n)
                                and pb_type = if fcall then (List.hd tl).typ else (List.nth tl  (pred n)).typ
                                and pb_loc  = if fcall then l.loc            else (List.nth !$l (pred n)).loc in
        raise (TypeError (pb_loc, "This expression of type " ^ typ_to_string pb_type ^ " is supposed to have type " ^ typ_to_string supposed_type ^ " as " ^ ordinal n ^ " returned value"))
    | AssMism0     (n1, n2)  -> raise (AssignmentMismatch (l.loc, string_of_int n2 ^ " values returned instead of " ^ string_of_int n1 ^ "\nType wanted: (" ^ typ_to_string return_type0 ^ "); type received: (" ^ typ_to_string (Prod types) ^ ")"))
    | MissingLoc_n (n, s)    -> let loc = if fcall then l.loc else (List.nth !$l (pred n)).loc in
                                raise (TypeError (loc, s))
  end;
  locals, stmt, true

and assign                             globals           locals0 (l1,               (l2: Parse.params)) =
  let locals1, tl1, types1 = try fold_map_args tlexpr globals locals0   l1     with NotALValue loc -> raise (SyntaxError (loc, "Cannot assign to such a value; expected name, attribute or indirection")) in
  let locals2, tl2, types2 =     fold_map_args texpr  globals locals1 !$l2 in
  let types2', stmt, fcall = match types2, tl2 with
  | [Prod []],                   [{desc = (Ecall_l (id, _, _) | Ecall_f (id, _, _, _)); typ=_}]       -> raise (SyntaxError (l2.loc, "Cannot use the call to " ^ id ^ " as a value"))
  | [Prod (_ :: _ :: _ as lst)], [{desc = (Ecall_l _          | Ecall_f _            ); typ=_} as el] -> lst, Sassignf (tl1, el),              true
  | lst,                         _lst2                                                                -> lst, Sassign  (List.combine tl1 tl2), false
  in
  begin try match_typ (Prod types1) (Prod types2') l2.loc
  with
    | TypeMismatch n         -> let supposed_type = List.nth types1 (pred n)
                                and pb_type = if fcall then (List.hd tl2).typ else (List.nth tl2  (pred n)).typ
                                and pb_loc  = if fcall then l2.loc            else (List.nth !$l2 (pred n)).loc in
                                let suffix_mult_assignment = if List.length types2' > 1 then " as type of the " ^ ordinal n ^ " variable being assigned to" else "" in
        raise (TypeError (pb_loc, "This expression of type " ^ typ_to_string pb_type ^ " is supposed to have type " ^ typ_to_string supposed_type ^ suffix_mult_assignment))
    | AssMism0 (n1, n2)      -> raise (AssignmentMismatch (l2.loc, string_of_int n2 ^ " values given for " ^ string_of_int n1 ^ "variables"))
    | MissingLoc_n (n, s)    -> let loc = if fcall then l2.loc else (List.nth !$l2 (pred n)).loc in
                                raise (TypeError (loc, s))
  end;
  locals2, stmt, false

and decl2 ((types, _, _, _)         as globals: globals) locals0 (l1, typ,          (l2: Parse.params)) =
  let tl1 = List.map (fun name -> !$name) l1
  and locals, tl2, types2 = fold_map_args texpr globals locals0 !$l2 in
  let types2', stmt, fcall = match types2, tl2 with
    | [Prod []],                   [{desc = (Ecall_l (id, _, _) | Ecall_f (id, _, _, _)); typ=_}]       -> raise (SyntaxError (l2.loc, "Cannot use the call to " ^ id ^ " as a value"))
    | [Prod (_ :: _ :: _ as lst)], [{desc = (Ecall_l _          | Ecall_f _            ); typ=_} as el] -> lst, Sdeclf (tl1, el),               true
    | lst,                         lst2                                                                 -> lst, Sdecl  (List.combine tl1 lst2), false
  in
  let types1 = match typ with
    | None     -> types2'
    | Some typ -> List.map (fun _ -> check_type types typ) types2'   (* Same length *)
  in
  if types1 = [VoidPoint] then raise (TypeError (l2.loc, "A type must be given to nil"));
  begin try match_typ (Prod types1) (Prod types2') l2.loc
  with
    | TypeMismatch n           -> let supposed_type = List.nth types1 (pred n)
                                  and pb_type = if fcall then (List.hd tl2).typ else (List.nth tl2  (pred n)).typ
                                  and pb_loc  = if fcall then l2.loc            else (List.nth !$l2 (pred n)).loc in
        raise (TypeError (pb_loc, "This expression of type " ^ typ_to_string pb_type ^ " is supposed to have type " ^ typ_to_string supposed_type ^ " as type of the " ^ ordinal n ^ " variable being declared"))
    | AssMism0     (n1, n2)    -> raise (AssignmentMismatch (l2.loc, string_of_int n2 ^ " values given for " ^ string_of_int n1 ^ "variables"))
    | MissingLoc_n (n, s)      -> let loc = if fcall then l2.loc else (List.nth !$l2 (pred n)).loc in
                                  raise (TypeError (loc, s))
  end;
  let vars = List.combine l1 types1 in
  let locals2 = List.fold_left (add_var types) locals vars in
  locals2, stmt, false


and decl  ((types, _, _, _)         as globals: globals) locals  (l1, typ,           l2) loc =
  match typ, l2 with
    | (None,     None)     -> raise (SyntaxError (loc, "This declaration should include a type or a value"))
    | (Some typ, None)     -> let vars = List.map (fun id -> id, typ) l1 in
                              let locals2 = List.fold_left (add_var types) locals vars in
                                locals2, Sdecl (List.map (fun name -> (!$name, package Cempty (check_type types typ))) l1), false
    | (_,        Some l2') -> decl2 globals locals (l1, typ, l2')

and binop ((_, structs_env, _, _)   as globals: globals) locals loc (op, e1, e2) =
  let locals1, te1 = texpr globals locals  e1 in
  let locals2, te2 = texpr globals locals1 e2 in
  begin match op with
    | Badd | Bsub | Bmul       -> match_typ (Prim "int")  te1.typ e1.loc; match_typ (Prim "int")  te2.typ e2.loc; locals2, package (Ebinop (op, te1, te2)) (Prim "int")
    | Bdiv | Bmod              -> match_typ (Prim "int")  te1.typ e1.loc; match_typ (Prim "int")  te2.typ e2.loc;
                                     if te2.desc = Cint 0L then raise (TypeError (e2.loc, "Cannot divide by 0")); locals2, package (Ebinop (op, te1, te2)) (Prim "int")
    | Blt  | Ble  | Bgt | Bge  -> match_typ (Prim "int")  te1.typ e1.loc; match_typ (Prim "int")  te2.typ e2.loc; locals2, package (Ebinop (op, te1, te2)) (Prim "bool")
    | Band | Bor               -> match_typ (Prim "bool") te1.typ e1.loc; match_typ (Prim "bool") te2.typ e2.loc; locals2, package (Ebinop (op, te1, te2)) (Prim "bool")
    | Beq  | Bneq              ->
        let stru = match te1.typ, te2.typ with
          | Prod _,    _         -> raise (TypeError (e1.loc,   "Cannot use a multi-valued function with other values"))
          | _,         Prod _    -> raise (TypeError (e2.loc,   "Cannot use a multi-valued function with other values"))
          | VoidPoint, VoidPoint -> raise (TypeError (loc,      "Operators == and != are not defined on nil"))
          | VoidPoint, typ       -> match_typ typ  VoidPoint e2.loc; ""
          | typ,       VoidPoint -> match_typ typ  VoidPoint e1.loc; ""
          | Prim t1,   typ2      when Smap.mem t1 structs_env ->
                                    match_typ (Prim t1) typ2 e2.loc; t1
          | typ1,      typ2      -> match_typ typ1      typ2 e2.loc; ""
        in
        if stru = "" then
          locals2, package (Ebinop (op, te1, te2)) (Prim "bool")
        else
          let attributes = Smap.find stru structs_env in
          let binop = match op with
            | Beq  -> Band
            | Bneq -> Bor
            | _    -> failwith "Impossible"
          in
          let cmp_attr attr _ cmp0 =
            let ident = Parse.package loc attr
            in
            let cmp =
              Parse.package loc (
                Parse.Ebinop (op, Parse.package e1.loc (Parse.Eattr (e1, ident)),
                                  Parse.package e2.loc (Parse.Eattr (e2, ident)))
              )
            in
            if !$cmp0 = Parse.Cempty then
              cmp
            else
              Parse.package loc (Parse.Ebinop (binop, cmp0, cmp))
          in
          texpr globals locals2 (Smap.fold cmp_attr attributes (Parse.package loc Parse.Cempty))
  end

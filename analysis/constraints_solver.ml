open CommonAST
open StaticTypedPartialAST
open NetlistConstrainedAST

module IntEnv = Map.Make (Int)

let debug = 0
let log i =
  if debug >= i then
    Format.printf
  else
    Format.ifprintf Format.std_formatter

type ternary =
  | Yes
  | No
  | Maybe

let b_to_t = function
  | true -> Yes
  | false -> No

(* let (&&) a b = match a, b with
  | No, _
  | _, No -> No
  | Yes, Yes -> Yes
  | _, _ -> Maybe *)

let (&&?) a b = match a, b with
  | Yes, Yes -> Yes
  | _, _ -> Maybe


type unknown_description =
  | VarDim of ident * int
  | Param of ident_desc * Location.location * int

type new_context =
  | Uid of UIDUnknownStatic.t
  | Recontextualize of static_bitype_exp list * new_context

and static_int_exp_desc =
  | UInt      of int
  | UIParam   of parameter
  | UIConst   of ident
  | UIUnknown of unknown_description * new_context
  | UIUnOp    of        int_unop * static_int_exp
  | UIBinOp   of          int_op * static_int_exp * static_int_exp
  | UISum     of static_int_exp list
  | UIIf      of static_bool_exp * static_int_exp * static_int_exp  (* se1 ? se2 : se3 *)

and static_bool_exp_desc =
  | UBool     of bool
  | UBParam   of parameter
  | UBConst   of ident
  | UBUnknown of unknown_description * new_context
  | UBUnOp    of       bool_unop * static_bool_exp
  | UBBinOp   of         bool_op * static_bool_exp * static_bool_exp
  | UBBinIntOp of    int_bool_op * static_int_exp  * static_int_exp
  | UBIf      of static_bool_exp * static_bool_exp * static_bool_exp  (* se1 ? se2 : se3 *)

and static_int_exp  = static_int_exp_desc  localized
and static_bool_exp = static_bool_exp_desc localized

and static_bitype_exp_desc =
  | UIntExp  of static_int_exp_desc
  | UBoolExp of static_bool_exp_desc
and static_bitype_exp = static_bitype_exp_desc localized

let sintexp = fun se -> SIntExp se


(* ------------------------------------------------------------------------------------------------------ *)

open Format
open Printers.CommonAst
open Printers.StaticTypedPartialAst

let print_desc = function
  | VarDim (name, i) -> dprintf "%s.%i" !*!name i
  | Param (fname, _, i) -> dprintf "%s#%i" fname i

let rec print_unknown d = function
  | Uid uid ->
      dprintf "?%a(%t)"
        UIDUnknownStatic.print uid
        (print_desc d)
  | Recontextualize (params, r) ->
      dprintf "%t%t"
        (print_unknown d r)
        (print_list brak comma_sep print_bitype_exp params)

and print_int_exp_desc = function
  | UInt n     -> dprintf "%i" n
  | UIParam i  -> dprintf "%s#%i" i.id_desc i.id_uid
  | UIUnknown (d, nc) ->
        print_unknown d nc
  | UIConst id -> print_ident id
  | UIUnOp (sunop, se) ->
      dprintf "%t%t"
        (print_int_unop sunop)
        (print_int_exp se)
  | UIBinOp (sop, se1, se2) ->
      par @@ dprintf "%t%t%t"
        (print_int_exp se1)
        (binop_sep (print_int_op sop))
        (print_int_exp se2)
  | UISum l ->
      print_list par (binop_sep "+") print_int_exp l
  | UIIf (c, se1, se2) ->
      par @@ dprintf "@[<hv 2>%t ?@ %t@ : %t@]"
        (print_bool_exp c)
        (print_int_exp se1)
        (print_int_exp se2)

and print_bool_exp_desc = function
  | UBool b    -> dprint_bool b
  | UBParam i  -> dprintf "%s#%i" i.id_desc i.id_uid
  | UBConst id -> print_ident id
  | UBUnknown (d, nc) ->
      print_unknown d nc
  | UBUnOp (sunop, se) ->
      par @@ dprintf "%t %t"
        (print_bool_unop sunop)
        (print_bool_exp se)
  | UBBinOp (sop, se1, se2) ->
      par @@ dprintf "%t%t%t"
        (print_bool_exp se1)
        (binop_sep (print_bool_op sop))
        (print_bool_exp se2)
  | UBBinIntOp (sop, se1, se2) ->
      par @@ dprintf "%t%t%t"
        (print_int_exp se1)
        (binop_sep (print_int_bool_op sop))
        (print_int_exp se2)
  | UBIf (c, se1, se2) ->
      par @@ dprintf "@[<hv 2>%t ?@ %t@ : %t@]"
        (print_bool_exp c)
        (print_bool_exp se1)
        (print_bool_exp se2)

and print_int_exp se = print_int_exp_desc se.desc
and print_bool_exp se = print_bool_exp_desc se.desc

and print_bitype_exp_desc = function
  | UIntExp  se -> print_int_exp_desc se
  | UBoolExp se -> print_bool_exp_desc se
and print_bitype_exp se = print_bitype_exp_desc se.desc

let print_opt_int_exp_desc = function
  | SUnknown uid ->
      dprintf "?%a" UIDUnknownStatic.print uid
  | SExp se -> print_int_exp_desc se

let print_opt_int_exp se = print_opt_int_exp_desc se.desc


let rec print_presize = function
  | PSVar (id, i, uid) -> print_unknown (VarDim (id, i)) (Uid uid)
  | PSConst se -> Printers.StaticTypedPartialAst.print_int_exp se
  | PSOtherContext (fname, _loc, params, ps) ->
      dprintf "@[<hv>(@;<0 2>(* %s *)@ %t@;<0 -2>)@]%t"
        fname
        (print_presize ps)
        (print_list brak comma_sep Printers.StaticTypedPartialAst.print_unknown_exp params)

let print_guard = function
  | SBool true ->
      dprintf ""
  | e ->
      dprintf "Under condition @[%t@],@;<1 2>" (Printers.StaticTypedPartialAst.print_bool_exp_desc e)

let print_constraints (l: constraints) =
  print_list (dprintf "%t") (dprintf "@.")
    (fun (g, (a, b)) ->
      dprintf "%t@[%t =@;<1 2>%t@]"
        (print_guard !!g)
        (print_presize a)
        (print_presize b)) l

(* ---------------------------------------------------------------------------------- *)


module UIDEnv = Map.Make (UIDUnknownStatic)

type union_find =
  | Link of unknown_description * UIDUnknownStatic.t
  | Indirect of Location.location * union_find
  | Direct of StaticTypedPartialAST.static_bitype_exp

type env = union_find UIDEnv.t

(* ----------------------------------------------------------------------------------- *)

let rec print_union_find = function
  | Link (d, uid) -> dprintf "%t@ ?%a" (par @@ print_desc d) UIDUnknownStatic.print uid
  | Indirect (_loc, un) -> dprintf "(loc) =@ %t" @@ print_union_find un
  | Direct exp -> dprintf "@[%t@]" (Printers.StaticTypedPartialAst.print_bitype_exp exp)

let print_env uid union_find =
  dprintf "?%a = @[%t@]"
    UIDUnknownStatic.print uid
    (print_union_find union_find)

(* ----------------------------------------------------------------------------------- *)

let rec mem uid env = match UIDEnv.find_opt uid env with
  | None -> false
  | Some thing -> mem' env thing
and mem' env = function
  | Link (_, uid) -> mem uid env
  | Direct _ -> true
  | Indirect (_, link) -> mem' env link

let rec find_opt uid env = match UIDEnv.find_opt uid env with
  | None -> None
  | Some thing -> find_opt' env thing
and find_opt' env = function
  | Link (_, uid) -> find_opt uid env
  | Direct se -> Some !!se
  | Indirect (_, link) -> find_opt' env link

let rec add uid el env = match UIDEnv.find_opt uid env with
  | None -> UIDEnv.add uid el env
  | Some thing -> add' el env thing
and add' el env = function
  | Link (_, uid) -> add uid el env
  | Direct _ -> invalid_arg "add'"
  | Indirect (_, link) -> add' el env link


let rec to_uiexp = function
  | SInt n -> UInt n
  | SIConst id -> UIConst id
  | SIParam i -> UIParam i
  | SIUnOp (op, se) -> UIUnOp (op, relocalize_fun to_uiexp se)
  | SIBinOp (op, se1, se2) -> UIBinOp (op, relocalize_fun to_uiexp se1, relocalize_fun to_uiexp se2)
  | SIIf (c, se1, se2) -> UIIf (relocalize_fun to_ubexp c, relocalize_fun to_uiexp se1, relocalize_fun to_uiexp se2)

and to_ubexp = function
  | SBool b -> UBool b
  | SBConst id -> UBConst id
  | SBParam i -> UBParam i
  | SBUnOp (op, se) -> UBUnOp (op, relocalize_fun to_ubexp se)
  | SBBinOp (op, se1, se2) -> UBBinOp (op, relocalize_fun to_ubexp se1, relocalize_fun to_ubexp se2)
  | SBBinIntOp (op, se1, se2) -> UBBinIntOp (op, relocalize_fun to_uiexp se1, relocalize_fun to_uiexp se2)
  | SBIf (c, se1, se2) -> UBIf (relocalize_fun to_ubexp c, relocalize_fun to_ubexp se1, relocalize_fun to_ubexp se2)

let to_ubiexp fname loc arg_nb = function
  | SOIntExp  (SUnknown uid) -> UIntExp  (UIUnknown (Param (fname, loc, arg_nb), Uid uid))
  | SOBoolExp (SUnknown uid) -> UBoolExp (UBUnknown (Param (fname, loc, arg_nb), Uid uid))
  | SOIntExp  (SExp se) -> UIntExp (to_uiexp se)
  | SOBoolExp (SExp se) -> UBoolExp (to_ubexp se)

let rec aux_substitute_int params se =
  let reloc = relocalize !@se in
  match !!se with
  | UInt n ->                     reloc @@ UInt n
  | UIConst id ->                 reloc @@ UIConst id
  | UIParam i ->                  begin
      match List.nth_opt params !**i with
        | None ->                                failwith "Param list too short"
        | Some { desc = UBoolExp _; loc = _ } -> failwith "Static type error"
        | Some { desc = UIntExp se; loc } ->     relocalize loc se
      end
  | UIUnknown (d, nc) ->          reloc @@ UIUnknown (d, Recontextualize (params, nc))
  | UIUnOp (op, se) ->            reloc @@ UIUnOp (op, aux_substitute_int params se)
  | UIBinOp (op, se1, se2) ->     reloc @@ UIBinOp (op, aux_substitute_int params se1, aux_substitute_int params se2)
  | UISum l ->                    reloc @@ UISum (List.map (aux_substitute_int params) l)
  | UIIf (c, se1, se2) ->         reloc @@ UIIf (aux_substitute_bool params c, aux_substitute_int params se1, aux_substitute_int params se2)

and aux_substitute_bool params se =
  let reloc = relocalize !@se in
  match !!se with
  | UBool b ->                    reloc @@ UBool b
  | UBConst id ->                 reloc @@ UBConst id
  | UBParam i ->                  begin
    match List.nth_opt params !**i with
      | None ->                                failwith "Param list too short"
      | Some { desc = UIntExp _; loc = _ } ->  failwith "Static type error"
      | Some { desc = UBoolExp se; loc } ->    relocalize loc se
    end
  | UBUnknown (d, nc) ->          reloc @@ UBUnknown (d, Recontextualize (params, nc))
  | UBUnOp (op, se) ->            reloc @@ UBUnOp (op, aux_substitute_bool params se)
  | UBBinOp (op, se1, se2) ->     reloc @@ UBBinOp (op, aux_substitute_bool params se1, aux_substitute_bool params se2)
  | UBBinIntOp (op, se1, se2) ->  reloc @@ UBBinIntOp (op, aux_substitute_int params se1, aux_substitute_int params se2)
  | UBIf (c, se1, se2) ->         reloc @@ UBIf (aux_substitute_bool params c, aux_substitute_bool params se1, aux_substitute_bool params se2)

let rec substitute_params_int = function
  | [] -> Fun.id
  | [params] -> aux_substitute_int params
  | params :: tl -> fun se -> substitute_params_int tl @@ aux_substitute_int params @@ se

let rec substitute_params_bool = function
  | [] -> Fun.id
  | [params] -> aux_substitute_bool params
  | params :: tl -> fun se -> substitute_params_bool tl @@ aux_substitute_bool params @@ se

let rec extract_uid = function
  | Recontextualize (_, e) -> extract_uid e
  | Uid uid -> uid

let rec extract_params acc = function
  | Recontextualize (p, nc) -> extract_params (p :: acc) nc
  | Uid _ -> acc


let rec substitute_env_int env se =
  let reloc = relocalize !@se in
  match !!se with
  | UInt n ->                     reloc @@ UInt n
  | UIConst id ->                 reloc @@ UIConst id
  | UIParam i ->                  reloc @@ UIParam i
  | UIUnknown (d, nc) ->          begin
      match find_opt (extract_uid nc) env with
      | None ->             reloc @@ UIUnknown (d, nc)
      | Some SBoolExp _ ->  failwith "Static type error"
      | Some SIntExp se ->
        let p_list = extract_params [] nc in
        substitute_env_int env @@
        substitute_params_int p_list (reloc @@ to_uiexp se)
    end
  | UIUnOp (op, se) ->            reloc @@ UIUnOp (op, substitute_env_int env se)
  | UIBinOp (op, se1, se2) ->     reloc @@ UIBinOp (op, substitute_env_int env se1, substitute_env_int env se2)
  | UISum l ->                    reloc @@ UISum (List.map (substitute_env_int env) l)
  | UIIf (c, se1, se2) ->         reloc @@ UIIf (substitute_env_bool env c, substitute_env_int env se1, substitute_env_int env se2)

and substitute_env_bool env se =
  let reloc = relocalize !@se in
  match !!se with
  | UBool b ->                    reloc @@ UBool b
  | UBConst id ->                 reloc @@ UBConst id
  | UBParam i ->                  reloc @@ UBParam i
  | UBUnknown (d, nc) ->          begin
      match find_opt (extract_uid nc) env with
      | None ->           reloc @@ UBUnknown (d, nc)
      | Some SIntExp _ -> failwith "Static type error"
      | Some SBoolExp se ->
        let p_list = extract_params [] nc in
        substitute_env_bool env @@
        substitute_params_bool p_list (reloc @@ to_ubexp se)
    end
  | UBUnOp (op, se) ->            reloc @@ UBUnOp (op, substitute_env_bool env se)
  | UBBinOp (op, se1, se2) ->     reloc @@ UBBinOp (op, substitute_env_bool env se1, substitute_env_bool env se2)
  | UBBinIntOp (op, se1, se2) ->  reloc @@ UBBinIntOp (op, substitute_env_int env se1, substitute_env_int env se2)
  | UBIf (c, se1, se2) ->         reloc @@ UBIf (substitute_env_bool env c, substitute_env_bool env se1, substitute_env_bool env se2)




let rec presize_to_uiexp = function
  | PSVar (name, i, uid) -> relocalize !*@name (UIUnknown (VarDim (name, i), Uid uid))
  | PSConst se -> relocalize_fun to_uiexp se
  | PSOtherContext (fname, loc, params, ps) ->
      let f_param i = relocalize_fun (to_ubiexp fname loc i) in
      aux_substitute_int (List.mapi f_param params) (presize_to_uiexp ps)

let rec from_uiexp = function
  | UInt n -> SInt n
  | UIConst id -> SIConst id
  | UIParam i -> SIParam i
  | UIUnknown _ -> invalid_arg "from_uiexp"
  | UIUnOp (op, se) -> SIUnOp (op, relocalize_fun from_uiexp se)
  | UIBinOp (op, se1, se2) -> SIBinOp (op, relocalize_fun from_uiexp se1, relocalize_fun from_uiexp se2)
  | UISum (hd :: tl) -> !! (List.fold_left (fun a b -> relocalize !@a @@ SIBinOp (SAdd, a, b)) (relocalize_fun from_uiexp hd) (List.map (relocalize_fun from_uiexp) tl))
  | UISum [] -> SInt 0
  | UIIf (c, se1, se2) -> SIIf (relocalize_fun from_ubexp c, relocalize_fun from_uiexp se1, relocalize_fun from_uiexp se2)

and from_ubexp = function
  | UBool b -> SBool b
  | UBConst id -> SBConst id
  | UBParam i -> SBParam i
  | UBUnknown _ -> invalid_arg "from_ubexp"
  | UBUnOp (op, se) -> SBUnOp (op, relocalize_fun from_ubexp se)
  | UBBinOp (op, se1, se2) -> SBBinOp (op, relocalize_fun from_ubexp se1, relocalize_fun from_ubexp se2)
  | UBBinIntOp (op, se1, se2) -> SBBinIntOp (op, relocalize_fun from_uiexp se1, relocalize_fun from_uiexp se2)
  | UBIf (c, se1, se2) -> SBIf (relocalize_fun from_ubexp c, relocalize_fun from_ubexp se1, relocalize_fun from_ubexp se2)

let rec no_free_variable_int env e = match !!e with
  | UInt _ | UIConst _ | UIParam _ -> true
  | UIUnknown (_, nc) -> if mem (extract_uid nc) env then no_free_variable_int env @@ substitute_env_int env @@ e else false
  | UIUnOp (_, se) -> no_free_variable_int env se
  | UIBinOp (_, se1, se2) -> no_free_variable_int env se1 && no_free_variable_int env se2
  | UISum l -> List.for_all (fun e -> no_free_variable_int env e) l
  | UIIf (c, se1, se2) -> no_free_variable_bool env c && no_free_variable_int env se1 && no_free_variable_int env se2

and no_free_variable_bool env e = match !!e with
  | UBool _ | UBConst _ | UBParam _ -> true
  | UBUnknown (_, nc) -> if mem (extract_uid nc) env then no_free_variable_bool env @@ substitute_env_bool env @@ e else false
  | UBUnOp (_, se) -> no_free_variable_bool env se
  | UBBinOp (_, se1, se2) -> no_free_variable_bool env se1 && no_free_variable_bool env se2
  | UBBinIntOp (_, se1, se2) -> no_free_variable_int env se1 && no_free_variable_int env se2
  | UBIf (c, se1, se2) -> no_free_variable_bool env c && no_free_variable_bool env se1 && no_free_variable_bool env se2


let rec maybe_equal_int = function
  | UInt n1,    UInt n2 -> b_to_t (n1 = n2)
  | UIParam i1, UIParam i2 -> b_to_t (!**i1 = !**i2)
  | UIConst v1, UIConst v2 -> b_to_t (!**v1 = !**v2)
  | UIUnknown (_, nc1), UIUnknown (_, nc2) -> b_to_t (extract_uid nc1 = extract_uid nc2)
  | (UInt _ | UIParam _ | UIConst _ | UIUnknown _), (UInt _ | UIParam _ | UIConst _ | UIUnknown _) -> Maybe   (* We don't want to rely on the equality of two value types -- missing ifs *)
  | UIUnOp (SNeg, se1), UIUnOp (SNeg, se2) -> maybe_equal_int (!!se1, !!se2)
  | UIBinOp (op, se1, se2), UIBinOp (op', se1', se2') -> if op <> op' then Maybe else maybe_equal_int (!!se1, !!se1') &&? maybe_equal_int (!!se2, !!se2')
  | UIIf (c, se1, se2), UIIf (c', se1', se2') -> maybe_equal_bool (!!c, !!c') &&? maybe_equal_int (!!se1, !!se2) &&? maybe_equal_int (!!se1', !!se2')
  | UISum l1, UISum l2 ->
    if List.length l1 <> List.length l2 then Maybe else
    List.fold_left (&&?) Yes @@ List.map maybe_equal_int @@ List.combine (List.map (!!) l1) (List.map (!!) l2)
  | _ -> Maybe

and maybe_equal_bool = function
  | UBool b1,   UBool b2 -> b_to_t (b1 = b2)
  | UBParam i1, UBParam i2 -> b_to_t (!**i1 = !**i2)
  | UBConst v1, UBConst v2 -> b_to_t (!**v1 = !**v2)
  | UBUnknown (_, nc1), UBUnknown (_, nc2) -> b_to_t (extract_uid nc1 = extract_uid nc2)
  | (UBool _ | UBParam _ | UBConst _ | UBUnknown _), (UBool _ | UBParam _ | UBConst _ | UBUnknown _) -> Maybe   (* We don't want to rely on the equality of two value types -- missing ifs *)
  | UBUnOp (SNot, se1), UBUnOp (SNot, se2) -> maybe_equal_bool (!!se1, !!se2)
  | UBBinOp (op, se1, se2), UBBinOp (op', se1', se2') -> if op <> op' then Maybe else maybe_equal_bool (!!se1, !!se2) &&? maybe_equal_bool (!!se1', !!se2')
  | UBIf (c, se1, se2), UBIf (c', se1', se2') -> maybe_equal_bool (!!c, !!c') &&? maybe_equal_bool (!!se1, !!se2) &&? maybe_equal_bool (!!se1', !!se2')
  | _ -> Maybe


let rec remove_minus se =
  let reloc = relocalize !@se in
  match !!se with
    | UIBinOp (SMinus, se1, se2) ->
        reloc @@ UIBinOp (SAdd, remove_minus se1, propagate_minus se2)
    | UIUnOp (SNeg, se) ->
        propagate_minus se
    | UInt _ | UIConst _ | UIParam _ | UIUnknown _ ->
        se
    | UIBinOp (SMult | SDiv as op, se1, {desc = UIUnOp (SNeg, se2); loc = _})
    | UIBinOp (SMult | SDiv as op, {desc = UIUnOp (SNeg, se1); loc = _}, se2) ->
        propagate_minus @@ reloc @@ UIBinOp (op, remove_minus se1, remove_minus se2)
    | UIBinOp (op, se1, se2) ->
        reloc @@ UIBinOp (op, remove_minus se1, remove_minus se2)
    | UISum l ->
        reloc @@ UISum (List.map remove_minus l)
    | UIIf (c, se1, se2) ->
        reloc @@ UIIf (c, remove_minus se1, remove_minus se2)


and propagate_minus se =
  let reloc = relocalize !@se in
  match !!se with
    | UIBinOp (SMult | SDiv as op, se1, {desc = UIUnOp (SNeg, se2); loc = _})
    | UIBinOp (SMult | SDiv as op, {desc = UIUnOp (SNeg, se1); loc = _}, se2) ->
        reloc @@ UIBinOp (op, remove_minus se1, remove_minus se2)
    | UIBinOp (SMult | SDiv as op, se1, se2) ->
        reloc @@ UIUnOp (SNeg, reloc @@ UIBinOp (op, remove_minus se1, remove_minus se2))
    | UIBinOp (SMinus, se1, se2) ->
        reloc @@ UIBinOp (SAdd, propagate_minus se1, remove_minus se2)
    | UIBinOp (SAdd, se1, se2) ->
        reloc @@ UIBinOp (SAdd, propagate_minus se1, propagate_minus se2)
    | UISum l ->
        reloc @@ UISum (List.map propagate_minus l)
    | UIBinOp (SPower, se1, se2) ->
        reloc @@ UIUnOp (SNeg, reloc @@ UIBinOp (SPower, remove_minus se1, remove_minus se2))
    | UIConst _ | UIParam _  | UIUnknown _ | UIIf _ ->
        reloc @@ UIUnOp (SNeg, se)
    | UInt n ->
        reloc @@ UInt (-n)
    | UIUnOp (SNeg, se) ->
        remove_minus se

let combine_order a b = if a <> 0 then a else b

let rec order a b = match !!a, !!b with
  | UIUnOp (_, s), s' -> order s (no_localize s')
  | s, UIUnOp (_, s') -> order (no_localize s) s'
  | UInt n, UInt n' -> n - n'
  | UInt _, _ -> -1
  | _, UInt _ -> 1
  | UIParam n, UIParam n' -> !**n - !**n'
  | UIParam _, _ -> -1
  | _, UIParam _ -> 1
  | UIConst n, UIConst n' -> UIDIdent.compare !**n !**n'
  | UIConst _, _ -> -1
  | _, UIConst _ -> 1
  | UIUnknown (_, n), UIUnknown (_, n') -> UIDUnknownStatic.compare (extract_uid n) (extract_uid n')
  | UIUnknown _, _ -> -1
  | _, UIUnknown _ -> 1

  | UIBinOp (op, s1, s2), UIBinOp (op', s1', s2') -> combine_order (compare op op') @@ combine_order (order s1 s1') (order s2 s2')
  | UIBinOp _, _ -> -1
  | _, UIBinOp _ -> 1
  | a, b -> compare a b

let rec sum_list l =
  log 10 "Sum_list0: @[%t@]@." (print_list_naked (binop_sep "+") print_int_exp l);
  let l = (List.sort order l) in
  log 10 "Sum_list1: @[%t@]@." (print_list_naked (binop_sep "+") print_int_exp l);
  let rec eat_ints = function
  | { desc = UInt 0; _ } :: tl -> tl
  | se' :: { desc = UIUnOp (SNeg, se); _ } :: tl when maybe_equal_int (!!se, !!se') = Yes -> tl
  | { desc = UIUnOp (SNeg, se); _ } :: se' :: tl when maybe_equal_int (!!se, !!se') = Yes -> tl
  | { desc = UInt n; loc } :: { desc = UInt n2; _ } :: tl -> eat_ints ({ desc = UInt (n+n2); loc } :: tl)
  | l -> l
  in
  let rec cancel acc = function
  | se' :: { desc = UIUnOp (SNeg, se); _ } :: tl when maybe_equal_int (!!se, !!se') = Yes -> cancel [] (List.rev_append acc tl)
  | { desc = UIUnOp (SNeg, se); _ } :: se' :: tl when maybe_equal_int (!!se, !!se') = Yes -> cancel [] (List.rev_append acc tl)
  | hd :: tl -> cancel (hd :: acc) tl
  | [] -> acc
  in
  let rec powers_of_2 acc = function
  | {desc=UIBinOp(SPower,{desc = UInt 2; _},n1);loc} :: {desc=UIBinOp(SPower,{desc = UInt 2; _},n2);_} :: tl
      when maybe_equal_int (!!n1, !!n2) = Yes ->
        powers_of_2 [] (List.rev_append acc
        ({desc=UIBinOp(SPower,{desc = UInt 2; loc},{desc=UIBinOp(SAdd,n1,{desc=UInt 1;loc});loc});loc} :: tl))
  | {desc=UIUnOp(SNeg,({desc=UIBinOp(SPower,{desc = UInt 2; _},n1);_} as se));loc} :: {desc=UIBinOp(SPower,{desc = UInt 2; _},n2);_} :: tl
      when maybe_equal_int ((!!) @@ single_treatment (relocalize loc (UIBinOp (SMinus, n2, n1))), UInt 1) = Yes ->
        powers_of_2 [] (List.rev_append acc (se :: tl))
  | {desc=UIBinOp(SPower,{desc = UInt 2; _},n2);_} :: {desc=UIUnOp(SNeg,({desc=UIBinOp(SPower,{desc = UInt 2; _},n1);_} as se));loc} :: tl
      when maybe_equal_int ((!!) @@ single_treatment (relocalize loc (UIBinOp (SMinus, n2, n1))), UInt 1) = Yes ->
        powers_of_2 [] (List.rev_append acc (se :: tl))
  | hd :: tl -> powers_of_2 (hd :: acc) tl
  | [] -> acc
  in
  let l = eat_ints l in
  log 10 "Sum_list2: @[%t@]@." (print_list_naked (binop_sep "+") print_int_exp l);
  let l = cancel [] l in
  log 10 "Sum_list3: @[%t@]@." (print_list_naked (binop_sep "+") print_int_exp l);
  let l = powers_of_2 [] l in
  log 10 "Sum_list4: @[%t@]@." (print_list_naked (binop_sep "+") print_int_exp l);
  match l with
  | [e] -> !!e
  | l -> UISum (List.rev @@ List.sort order l)


and sums se =
  relocalize !@se @@
  match !!se with
    | UIBinOp (SMinus, _, _) -> failwith "Should have removed minus first"
    | UIUnOp (SNeg, se) ->
        UIUnOp (SNeg, sums se)
    | UInt _ | UIConst _ | UIParam _ | UIUnknown _ ->
        !!se
    | UIBinOp (SAdd, se1, se2) ->
        (sum_list (add_sum se1 @ add_sum se2))
    | UIBinOp (SMult, se1, se2) ->
        sum_list @@
          List.concat_map (fun se2 -> List.map (fun se1 -> relocalize !@se @@ UIBinOp (SMult, se1, se2)) (add_sum se1)) (add_sum se2)
    | UIBinOp (op, se1, se2) ->
        UIBinOp (op, sums se1, sums se2)
    | UISum l ->
        (sum_list (List.concat_map add_sum l))
    | UIIf (c, se1, se2) ->
        UIIf (c, sums se1, sums se2)


and add_sum se =
  let reloc = relocalize !@se in
  match !!se with
    | UIBinOp (SMinus, _, _) -> failwith "Should have removed minus first"
    | UIUnOp (SNeg, se) ->
        [reloc (UIUnOp (SNeg, sums se))]
    | UInt _ | UIConst _ | UIParam _ | UIUnknown _ ->
        [se]
    | UIBinOp (SAdd, se1, se2) ->
        (add_sum (sums se1) @ add_sum (sums se2))
    | UIBinOp (SMult, se1, se2) ->
        List.concat_map (fun se2 -> List.map (fun se1 -> reloc @@ UIBinOp (SMult, se1, se2)) (add_sum se1)) (add_sum se2)
    | UIBinOp (op, se1, se2) ->
        [reloc @@ UIBinOp (op, sums se1, sums se2)]
    | UISum l ->
        l
    | UIIf (c, se1, se2) ->
        [reloc @@ UIIf (c, sums se1, sums se2)]



and evaluate_consts s se =
  let f_of_op = function
  | SAdd -> (+) | SMinus -> (-)
  | SMult -> ( * ) | SDiv -> (/) | SPower -> Misc.exp
  in
  let reloc = relocalize !@se in
  match !!se with
    | UIParam i when IntEnv.mem !**i s ->
        evaluate_consts s (no_localize @@ IntEnv.find !**i s)
    | UInt _ | UIConst _ | UIParam _ | UIUnknown _ ->
        se
    | UIUnOp (SNeg, se1) -> begin
      let se1' = evaluate_consts s se1 in
      match !!se1' with
      | UInt n -> reloc @@ UInt (-n)
      | _ -> se
      end
    | UIBinOp (op, se1, se2) -> begin
        let se1' = evaluate_consts s se1 in
        let se2' = evaluate_consts s se2 in
        match !!se1', !!se2' with
        | UInt n, UInt n2 -> reloc @@ UInt (f_of_op op n n2)
        | UInt 1, _ when op = SMult -> se2'
        | _, UInt 1 when op = SMult || op = SDiv -> se1'
        | UInt (-1), _ when op = SMult -> reloc @@ UIUnOp (SNeg, se2')
        | _, UInt (-1) when op = SMult || op = SDiv -> reloc @@ UIUnOp (SNeg, se1')
        | UInt 0, _ when op = SMult || op = SDiv -> reloc @@ UInt 0
        | _, UInt 0 when op = SMult  -> reloc @@ UInt 0
        | _ -> reloc @@ UIBinOp (op, se1', se2')
        end
    | UISum [] ->
        reloc @@ UInt 0
    | UISum [ui] ->
        evaluate_consts s ui
    | UISum l ->
        reloc @@ UISum (List.map (evaluate_consts s) l)
    | UIIf (c, se1, se2) ->
        reloc @@ UIIf (c, evaluate_consts s se1, evaluate_consts s se2)

and single_treatment a =
  sums @@ remove_minus @@ evaluate_consts IntEnv.empty a

let rec extract_guard = function
  | SBBinIntOp (SEq, {desc=SIParam i; _}, {desc; _})
  | SBBinIntOp (SEq, {desc; _}, {desc=SIParam i; _}) -> IntEnv.singleton !**i (to_uiexp desc)
  | SBBinOp (SAnd, se1, se2) -> IntEnv.union (fun _ a b -> assert (a = b); Some a) (extract_guard !!se1) (extract_guard !!se2)
  | SBBinOp (SOr, se1, se2) -> IntEnv.merge (fun _ a b -> match (a, b) with Some a, Some b -> assert (a = b); Some a | _ -> None) (extract_guard !!se1) (extract_guard !!se2)
  | SBool _ | SBConst _ | SBParam _
  | SBUnOp _ | SBIf _
  | SBBinIntOp _ -> IntEnv.empty


let rec count_unknowns env e = match !!e with
  | UInt _ | UIParam _ | UIConst _ -> 0
  | UIUnknown (_, u) -> if mem (extract_uid u) env then 0 else 1
  | UIUnOp (SNeg, s) -> count_unknowns env s
  | UIBinOp (_, s, s') -> count_unknowns env s + count_unknowns env s'
  | UIIf (_, _, _) -> 30 (* I don't want to work with these *)
  | UISum _ -> 40 (* Should be impossible *)

let balance env (a, b) = match !!a, !!b with
  | UISum l, _ when List.fold_left (+) 0 @@ List.map (count_unknowns env) l = 1 ->
      let u, l' = List.partition (fun s -> match !!s with UIUnknown (_, u) -> not @@ mem (extract_uid u) env | _ -> false) l in
      let u = match u with [u] -> u | _ -> assert false in
      u, relocalize !@b (UIBinOp (SMinus, b, relocalize !@a @@ UISum l'))
  | _, UISum l when List.fold_left (+) 0 @@ List.map (count_unknowns env) l = 1 ->
      let u, l' = List.partition (fun s -> match !!s with UIUnknown (_, u) -> not @@ mem (extract_uid u) env | _ -> false) l in
      let u = match u with [u] -> u | _ -> assert false in
      relocalize !@a (UIBinOp (SMinus, a, relocalize !@a @@ UISum l')), u
  | _ -> a, b



let pre_treatment env guard (a, b) =
  let s = extract_guard guard in
  let one_treatment e = sums @@ remove_minus @@ evaluate_consts s e in
  let enough_treatments e = one_treatment @@ one_treatment e in
  let (a, b) = enough_treatments a, enough_treatments b in
  let (a, b) = balance env (a, b) in
  let (a, b) = enough_treatments a, enough_treatments b in
  a, b






let analyze_result ue1 ue2 se1 se2 = function
  | Yes -> ()
  | Maybe ->
      Format.eprintf
        "%a@[<hv>Size warning: could not unite size @;<0 2>%t@;<0 -2>@]@ @[<hv>(simpl.@;<1 2>%t@;<1 -2>)@]@ \
        @[<hv>with expected size @;<0 2>%t@;<0 -2>@]@ @[<hv>(simpl.@;<1 2>%t@;<1 -2>)@]@ located here:@ %a@."
        Location.print_location !@ue2
        (print_int_exp ue2)
        (print_int_exp se2)
        (print_int_exp ue1)
        (print_int_exp se1)
        Location.print_location !@ue1
  | No ->
      Format.eprintf
        "%a@[<hv>Size error: could not unite size @;<0 2>%t@;<0 -2>@]@ @[<hv>(simpl.@;<1 2>%t@;<1 -2>)@]@ \
        @[<hv>with expected size @;<0 2>%t@;<0 -2>@]@ @[<hv>(simpl.@;<1 2>%t@;<1 -2>)@]@ located here:@ %a@."
        Location.print_location !@ue2
        (print_int_exp ue2)
        (print_int_exp se2)
        (print_int_exp ue1)
        (print_int_exp se1)
        Location.print_location !@ue1;
        raise Errors.ErrorDetected




let solve_constraint_one env guard (a', b') =
  log 4 "%t@." (print_guard !!guard);
  log 4 "@[%t et@;<1 2>%t@]@.@." (print_int_exp a') (print_int_exp b');
  let a, b = pre_treatment env (SBool true) (a', b') in
  log 5 "==> @[%t et@;<1 2>%t@]@.@." (print_int_exp a) (print_int_exp b);
  match !!a, !!b with
  | UIUnknown (d, Uid uid), UIUnknown (_, Uid uid') when not (mem uid env) ->
      add uid (Link (d, uid')) env, true
  | UIUnknown (_, Uid uid'), UIUnknown (d, Uid uid) when not (mem uid env) ->
      add uid (Link (d, uid')) env, true
  | UIUnknown (_, Uid uid), _ when not (mem uid env) && no_free_variable_int env b ->
      add uid (Direct (relocalize !@b @@ SIntExp (from_uiexp @@ (!!) @@ single_treatment @@ substitute_env_int env @@ b))) env, true
  | _, UIUnknown (_, Uid uid) when not (mem uid env) && no_free_variable_int env a ->
      add uid (Direct (relocalize !@b @@ SIntExp (from_uiexp @@ (!!) @@ single_treatment@@ substitute_env_int env @@ a))) env, true
  | _ when no_free_variable_int env a' && no_free_variable_int env b' ->
      let se1 = substitute_env_int env a' in
      let se2 = substitute_env_int env b' in
      log 5 "| @[%t et@;<1 2>%t@]@.@." (print_int_exp se1) (print_int_exp se2);
      let (se1', se2') = pre_treatment env !!guard (se1, se2) in
      log 5 "| ==> @[%t et@;<1 2>%t@]@.@." (print_int_exp se1') (print_int_exp se2');
      analyze_result a' b' se1' se2' @@ maybe_equal_int (!!se1', !!se2');
      env, true
  | _ ->
      env, false


let solve_constraints (l: NetlistConstrainedAST.constraints) =
  let env = UIDEnv.empty in

  let presize_to_uiexp2 (a, b) = (presize_to_uiexp a, presize_to_uiexp b) in
  let rec one_round env acc = function
    | [] -> env, acc
    | (guard, hd) :: tl ->
        let env, ok = solve_constraint_one env guard @@ presize_to_uiexp2 hd in
        log 4 "Found equalities@.";
        UIDEnv.iter (fun uid union -> log 4 "%t@." (print_env uid union)) env;
        log 4 "@.";
        if ok then
          one_round env acc tl
        else
          one_round env ((guard, hd) :: acc) tl
  in

  let rec repeat env l =
    let env', remaining = one_round env [] l in
    if env <> env' then
      repeat env' remaining
    else begin
      log 3 "%t" @@
      if List.length l > 0 then
        dprintf "@.Remaining unused constraints:@.%t@." (print_constraints remaining)
      else
        dprint_nop;
      env
    end
  in
  let (l_unguarded, l_guarded) = List.partition (fun (g1, _) -> match !!g1 with | SBool true -> true | _ -> false) l in
  log 1 "@.All constraints:@.%t@.@." (print_constraints l_unguarded);
  let env = repeat env l_unguarded in
  log 1 "@.All constraints:@.%t@.@." (print_constraints l_guarded);
  let env = repeat env l_guarded in
  log 1 "Found equalities@.";
  UIDEnv.iter (fun uid union -> log 1 "%t@." (print_env uid union)) env;
  log 1 "@.";
  env


(* let (<?) a b = match a, b with
  | UInt n, UInt n' -> n < n'
  | UIParam i, UIParam i' -> i < i'
  | UIConst v1, UIConst v2 -> !!v1 < !!v2
  | UIUnknown nc1, UIUnknown nc2 -> b_to_t (extract_uid nc1 = extract_uid nc2)
  | UIUnOp (SNeg, se1), UIUnOp (SNeg, se2) -> exactly_equal_int (!!se1, !!se2)
  | UIBinOp (op, se1, se2), UIBinOp (op', se1', se2') -> if op <> op' then No else exactly_equal_int (!!se1, !!se2) && exactly_equal_int (!!se1', !!se2')
  | UIIf (c, se1, se2), UIIf (c', se1', se2') -> exactly_equal_bool (!!c, !!c') && exactly_equal_int (!!se1, !!se2) && exactly_equal_int (!!se1', !!se2')


let rec normal_form = function
  | UInt n -> UInt n
  | UIParam i -> UIParam i
  | UIConst v -> UIConst v
  | UIUnOp (SNeg, se) -> UIUnop (SNeg, relocalize_fun normal_form se)
  | UIBinOp (SAdd, ({ desc = (UInt _ | UIParam _ | UIConst _ | UIUnOp (SNeg, _)); loc = _ } as se1),
                   ({ desc = (UInt _ | UIParam _ | UIConst _ | UIUnOp (SNeg, _)); loc = _ } as se2)) ->
        if !!se1 <? !!se2 then UIBinOp (SAdd, se1, se2) else UIBinOp (SAdd, se2, se1) *)


(* let rec solve_constraint env = function
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
      analyze_result c1 c2 @@ maybe_equal_int (!!se, !!se');
      env
  | (PSVar (_, _, uid) as c1), (PSConst se' as c2) ->
      let se = find uid env in
      analyze_result c1 c2 @@ maybe_equal_int (!!se, !!se');
      env
  | (PSConst se as c1), (PSVar (_, _, uid') as c2) ->
      let se' = find uid' env in
      analyze_result c1 c2 @@ maybe_equal_int (!!se, !!se');
      env
  | (PSConst se as c1), (PSConst se' as c2) ->
      analyze_result c1 c2 @@ maybe_equal_int (!!se, !!se');
      env *)

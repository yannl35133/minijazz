open Format
open CommonAST
open CommonAst
open StaticTypedPartialAST

(* Static expression *)

let print_int_op = function
  | SAdd -> "+" | SMinus -> "-" | SMult -> "*" | SDiv -> "/" | SPower -> "^"
let print_int_bool_op = function
  | SEq -> "=" | SNeq -> "!="
  | SLt -> "<" | SLeq -> "<=" | SGt -> ">" | SGeq -> ">="
let print_bool_op = function
  | SOr -> "||" | SAnd -> "&&"

let print_int_unop unop =
  let op_str =
    match unop with
    | SNeg -> "-"
  in
  dprintf "%s" op_str

let print_bool_unop unop =
  let op_str =
    match unop with
    | SNot -> "!"
  in
  dprintf "%s" op_str

let rec print_int_exp_desc = function
  | SInt n     -> dprintf "%i" n
  | SIParam i  -> dprintf "%s" i.id_desc
  | SIConst id -> print_ident id
  | SIUnOp (sunop, se) ->
      dprintf "%t %t"
        (print_int_unop sunop)
        (print_int_exp se)
  | SIBinOp (sop, se1, se2) ->
      dprintf "%t%t%t"
        (print_int_exp se1)
        (binop_sep (print_int_op sop))
        (print_int_exp se2)
  | SIIf (c, se1, se2) ->
      dprintf "@[<hv 2>%t ?@ %t@ : %t@]"
        (print_bool_exp c)
        (print_int_exp se1)
        (print_int_exp se2)

and print_bool_exp_desc = function
  | SBool b    -> dprint_bool b
  | SBParam i  -> dprintf "%s" i.id_desc
  | SBConst id -> print_ident id
  | SBUnOp (sunop, se) ->
      dprintf "%t %t"
        (print_bool_unop sunop)
        (print_bool_exp se)
  | SBBinOp (sop, se1, se2) ->
      dprintf "%t%t%t"
        (print_bool_exp se1)
        (binop_sep (print_bool_op sop))
        (print_bool_exp se2)
  | SBBinIntOp (sop, se1, se2) ->
      dprintf "%t%t%t"
        (print_int_exp se1)
        (binop_sep (print_int_bool_op sop))
        (print_int_exp se2)
  | SBIf (c, se1, se2) ->
      dprintf "@[<hv 2>%t ?@ %t@ : %t@]"
        (print_bool_exp c)
        (print_bool_exp se1)
        (print_bool_exp se2)

and print_int_exp se = print_int_exp_desc se.desc
and print_bool_exp se = print_bool_exp_desc se.desc

let print_unknown_exp_desc = function
  | SOIntExp  SUnknown uid | SOBoolExp SUnknown uid ->
      dprintf "?%a" UIDUnknownStatic.print uid
  | SOIntExp  SExp se -> print_int_exp_desc se
  | SOBoolExp SExp se -> print_bool_exp_desc se
let print_unknown_exp se = print_unknown_exp_desc se.desc

let print_bitype_exp_desc = function
  | SIntExp  se -> print_int_exp_desc se
  | SBoolExp se -> print_bool_exp_desc se
let print_bitype_exp se = print_bitype_exp_desc se.desc

let print_opt_int_exp_desc = function
  | SUnknown uid ->
      dprintf "?%a" UIDUnknownStatic.print uid
  | SExp se -> print_int_exp_desc se

let print_opt_int_exp se = print_opt_int_exp_desc se.desc

let print_static_type static_type =
  dprintf "%s" (static_type_to_string static_type)

let print_static_typed_ident = print_static_typed_ident print_static_type

(* State expressions *)

let rec print_state_exp_desc print_exp = function
  | EConstr id -> print_constructor id
  | ESMux (e, es1, es2) -> dprintf "mux@[<hv 2>(@,%t,@ %t,@ %t@;<0 -2>)@]"
      (print_exp e)
      (print_state_exp print_exp es1)
      (print_state_exp print_exp es2)
and print_state_exp print_exp s = print_state_exp_desc print_exp s.s_desc

let print_state_transition_exp_desc print_exp = function
  | EContinue s -> dprintf "continue %t" (print_state_exp print_exp s)
  | ERestart s -> dprintf "restart %t" (print_state_exp print_exp s)
let print_state_transition_exp print_exp s = print_state_transition_exp_desc print_exp s.st_desc

let print_tritype_exp print_exp = function
  | Exp e -> print_exp e
  | StateExp s -> print_state_exp print_exp s
  | StateTransitionExp st -> print_state_transition_exp print_exp st

(* Netlist expressions *)

let rec print_lvalue_desc print_netlist_type lval_desc =
  match lval_desc with
  | LValDrop    -> dprintf "_"
  | LValId id   -> print_ident id
  | LValTuple l -> print_list par comma_sep (print_lvalue print_netlist_type) l

and print_lvalue print_netlist_type lval =
  par (dprintf "%t: %t"
    (print_lvalue_desc print_netlist_type !?!lval)
    (print_netlist_type !??lval))


let print_const = print_const print_bitype_exp


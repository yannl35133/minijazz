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
  | SIParam i  -> dprintf "#%i" i
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
  | SBParam i  -> dprintf "#%i" i
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
      dprintf "?%a" UniqueId.print uid
  | SOIntExp  SExp se -> print_int_exp_desc se
  | SOBoolExp SExp se -> print_bool_exp_desc se
let print_unknown_exp se = print_unknown_exp_desc se.desc

let print_bitype_exp_desc = function
  | SIntExp  se -> print_int_exp_desc se
  | SBoolExp se -> print_bool_exp_desc se
let print_bitype_exp se = print_bitype_exp_desc se.desc

let print_opt_int_exp_desc = function
  | SUnknown uid ->
      dprintf "?%a" UniqueId.print uid
  | SExp se -> print_int_exp_desc se

let print_opt_int_exp se = print_opt_int_exp_desc se.desc



let print_stid_desc stid_desc =
  dprintf "%t: %s"
    (print_ident stid_desc.st_name)
    (static_type_to_string !!(stid_desc.st_type))

let print_stid stid = print_stid_desc stid.desc

(* Netlist expressions *)

let print_const (const_name, const) =
  dprintf "@[<hv 2>const %s%t%t@]"
    const_name
    (binop_sep "=")
    (print_bitype_exp const.const_decl)


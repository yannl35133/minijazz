open Format
open CommonAST
open CommonAst
open StaticTypedPartialAst
open StaticTypedAST

let print_size = print_opt_int_exp

let print_slice_param = print_slice_param print_size

(* Netlist expressions *)

let print_netlist_type = print_netlist_type print_size
let print_global_type = print_bitype print_netlist_type


let rec print_exp_desc = function
  | EConst v ->  print_val v
  | EVar id  ->  print_ident id
  | EConstr id -> print_constructor id
  | EContinue s -> dprintf "continue %t" (print_exp s)
  | ERestart s -> dprintf "restart %t" (print_exp s)
  | EReg e   ->  dprintf "reg@ %t" (print_exp e)
  | ESlice (params, arg) ->
      dprintf "%t%t"
        (print_exp arg)
        (print_list brak comma_sep print_slice_param params)
  | ESupOp (op, args) when !!op = "not" ->
      dprintf "%t%t"
        (print_funname op)
        (print_list par comma_sep print_exp args)
  | ESupOp (op, args) when !!op = "mux" ->
      dprintf "%t%t"
        (print_funname op)
        (print_list par comma_sep print_exp args)
  | ESupOp (op, args) when !!op = "add_dim" ->
      dprintf "%t"
        (print_list brak comma_sep print_exp args)
  | ESupOp (op, args) when !!op = "concat" ->
      let e1, e2 = Misc.assert_2 args in
      dprintf "@[<hv2>%t%t%t@]"
        (print_exp e1)
        (binop_sep ".")
        (print_exp e2)
  | ESupOp (op, args) ->
      let e1, e2 = Misc.assert_2 args in
      dprintf "@[<hv2>%t%t%t@]"
        (print_exp e1)
        (binop_sep op.desc)
        (print_exp e2)
  | ECall (fname, params, args) ->
      dprintf "%t@[<hv4>%t@,%t@]"
        (print_funname fname)
        (print_list_if_nonempty chev comma_sep print_unknown_exp params)
        (print_list par comma_sep print_exp args)
  | EMem (memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t, %t>(%t)"
        (print_mem_kind memkind)
        (print_opt_int_exp addr_size)
        (print_opt_int_exp word_size)
        (print_list_naked comma_sep print_exp args)

and print_exp exp = print_exp_desc exp.desc

let print_typed_ident = print_typed_ident print_size

let rec print_lvalue_desc = function
  | LValDrop    -> dprintf "_"
  | LValId id   -> print_ident id
  | LValTuple l -> print_list par comma_sep print_lvalue0 l

and print_lvalue0 lval = print_lvalue_desc !!lval

let is_lval_bit ti_type =
  match !!ti_type with
  | None -> true
  | Some BNetlist TNDim [] -> true
  | _ -> false

let print_lvalue { lval; lval_type } =
  dprintf "@[<hv2>%t%t@]"
    (print_lvalue0 lval)
    (dprint_if (not (is_lval_bit lval_type)) @@
      dprintf ":%t"
        (print_global_type (Option.get !!lval_type))
    )

let rec print_decl_desc = function
  | Deq (lv, exp) ->
      dprintf "@[%t%t%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_exp exp)
        (semicolon_sep)
  | Dlocaleq (lv, exp) ->
      dprintf "@[local %t%t%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_exp exp)
        (semicolon_sep)
  | Dreset (exp, eqs) ->
      dprintf "@[<hv2>reset@ %t@]@ every %t%t"
        (print_block print_decl eqs)
        (print_exp exp)
        (semicolon_sep)
  | Dautomaton auto ->
     dprintf "@[<v2>automaton@ %t@]@ end"
      (print_automaton (print_exp, print_exp, print_decl) auto)
  | Dmatch (e, matcher) ->
    dprintf "@[<v2>match %t with@ %t@]@ end"
      (print_exp e)
      (print_matcher print_decl matcher)
  | Dif (se, b1, b2) ->
     dprintf "@[if@ %t@ then@]@;<1 2>@[<v>%t@]@ else@;<1 2>@[<v>%t@]@ end if"
        (print_bool_exp se)
        (print_block print_decl b1)
        (print_block print_decl b2)

and print_decl eq = print_decl_desc eq.desc


let print_node n = print_node (print_static_type, print_size, print_decl) n
let print_program p = print_program (print_static_type, print_bitype_exp, print_size, print_decl) p

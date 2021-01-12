open Format
open CommonAST
open CommonAst
open ParserAST

(* Static expression *)

let print_ident (id: ident) = dprintf "%s" id.desc

let print_enum { enum_name; enum_constructors; _ } =
  dprintf "type %t =@[<hv2>@ %t@]@\n"
    (print_ident enum_name)
    (print_list_naked (dprintf " |@ ") print_ident enum_constructors)

let print_sop = function
  | SAdd -> "+" | SMinus -> "-" | SMult -> "*" | SDiv -> "/" | SPower -> "^"
  | SEq -> "=" | SNeq -> "!="
  | SLt -> "<" | SLeq -> "<=" | SGt -> ">" | SGeq -> ">="
  | SOr -> "||" | SAnd -> "&&"

let print_sunop unop =
  let op_str =
    match unop with
    | SNeg -> "-"
    | SNot -> "!"
  in
  dprintf "%s" op_str

let rec print_sexp_desc = function
  | SInt i    -> dprintf "%i" i
  | SBool b   -> dprint_bool b
  | SIdent id -> print_ident id
  | SPar se   -> par (print_sexp se)
  | SUnOp (sunop, se) ->
      dprintf "%t %t"
        (print_sunop sunop)
        (print_sexp se)
  | SBinOp (sop, se1, se2) ->
      dprintf "%t%t%t"
        (print_sexp se1)
        (binop_sep (print_sop sop))
        (print_sexp se2)
  | SIf (c, se1, se2) ->
      dprintf "@[<hv 2>%t ?@ %t@ : %t@]"
        (print_sexp c)
        (print_sexp se1)
        (print_sexp se2)

and print_sexp se : formatter -> unit = print_sexp_desc se.desc

let print_opt_sexp opt_se = print_static_opt print_sexp_desc opt_se.desc

let print_static_typed_ident { sti_name; sti_type; _} =
  dprintf "%t: %t"
    (print_ident sti_name)
    (print_ident sti_type)


(* Netlist expressions *)

let rec print_netlist_type = function
  | TNDim opt_se_l ->
    print_list brak comma_sep print_opt_sexp opt_se_l
  | TProd l ->
    print_list par star_sep print_netlist_type l

let print_global_type = function
  | BNetlist ti -> print_netlist_type ti
  | BState id ->
      print_ident id
  | BStateTransition id ->
      dprintf "%t transition"
        (print_ident id)

let print_slice_param = print_slice_param print_opt_sexp

let rec print_exp_desc = function
  | EConst v -> print_val v
  | EConstr c -> print_ident c
  | EVar id  -> print_ident id
  | EContinue e -> dprintf "continue %t" (print_exp e)
  | ERestart e ->  dprintf "restart %t" (print_exp e)
  | EPar e   -> par (print_exp e)
  | EReg e   -> dprintf "reg(%t)" (print_exp e)
  | ESlice (params, arg) ->
      dprintf "%t%t"
        (print_exp arg)
        (print_list brak comma_sep print_slice_param params)
  | ESupOp (op, args) when !!op = "not" ->
      dprintf "%t%t"
        (print_ident op)
        (print_list par comma_sep print_exp args)
  | ESupOp (op, args) when !!op = "add_dim" ->
      dprintf "%t"
        (print_list brak comma_sep print_exp args)
  | ESupOp (op, args) when !!op = "mux" ->
      dprintf "%t%t"
        (print_ident op)
        (print_list par comma_sep print_exp args)
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
      dprintf "%t@[<hv4>%t%t@]"
        (print_ident fname)
        (print_list_if_nonempty chev comma_sep print_opt_sexp params)
        (print_list par comma_sep print_exp args)
  | EMem (memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t, %t>(%t)"
        (print_mem_kind memkind)
        (print_opt_sexp addr_size)
        (print_opt_sexp word_size)
        (print_list_naked comma_sep print_exp args)

and print_exp exp fmt = print_exp_desc exp.desc fmt

let rec print_lvalue_desc lval_desc =
  match lval_desc with
  | LValDrop    -> dprintf "_"
  | LValId id   -> print_ident id
  | LValTuple l -> print_list par comma_sep print_lvalue l

and print_lvalue lval = print_lvalue_desc lval.desc


let is_bit ti_type =
  match !!ti_type with
  | BNetlist TNDim [] -> true
  | _ -> false


let print_typed_ident { ti_name; ti_type; _ } =
  dprintf "@[<hv2>%t%t@]"
    (print_ident ti_name)
    (dprint_if (not (is_bit ti_type)) @@
      dprintf ":%t"
        (print_global_type !!ti_type)
    )


let rec print_match_handler { m_state; m_body; _ } =
  dprintf "| %t ->@[<hv2>@ %t@]"
    (print_ident m_state)
    (print_block m_body)

and print_matcher { m_handlers; _ } = print_list_naked dprint_newline print_match_handler m_handlers

and print_transition =
  print_list_naked
    else_sep
    (fun (e1, e2) ->
      dprintf "%t then@[<2>@ %t@]"
        (print_exp e1)
        (print_exp e2))

and print_automaton_handler { a_state; a_body; a_weak_transition; a_strong_transition; _ } =
  dprintf "@[<hv2>| %t ->@ %t@ %t@ %t@]"
    (print_ident a_state)
    (print_block a_body)
    (dprint_if (a_weak_transition <> [])
      (dprintf "@[<hv2>until@ %t@]"
        (print_transition a_weak_transition)))
    (dprint_if (a_strong_transition <> [])
      (dprintf "@[<hv2>unless@ %t@]"
        (print_transition a_strong_transition)))

and print_automaton { a_handlers; _ } = print_list_naked dprint_newline print_automaton_handler a_handlers

and print_decl_desc = function
  | Deq (lv, exp) ->
      dprintf "@[<h>%t%t%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_exp exp)
        (semicolon_sep)
  | Dlocaleq (lv, exp) ->
      dprintf "@[<h>local %t%t%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_exp exp)
        (semicolon_sep)
  | Dreset (exp, eqs) ->
      dprintf "@[<hv2>reset@ %t@]@ every %t%t"
        (print_block eqs)
        (print_exp exp)
        (semicolon_sep)
  | Dautomaton auto ->
     dprintf "@[<v2>automaton@ %t@]@ end"
      (print_automaton auto)
  | Dmatch (e, matcher) ->
    dprintf "@[<v2>match %t with@ %t@]@ end"
      (print_exp e)
      (print_matcher matcher)
  | Dif (se, b1, b2) ->
     dprintf "@[if@ %t@ then@]@;<1 2>@[<v>%t@]@ else@;<1 2>@[<v>%t@]@ end if"
        (print_sexp se)
        (print_block b1)
        (print_block b2)

and print_decl eq = print_decl_desc eq.desc
and print_block b = print_list_naked dprint_newline print_decl b


let print_node { node_name; node_inline; node_inputs; node_outputs; node_params; node_body; _ } =
  dprintf "@[<v 2>@[<2>%t%t%t@,%t%t%t@;<1 -2>@]where@ %t@]@ end where"
    (print_inline_status node_inline)
    (print_ident node_name)
    (print_list_if_nonempty chev comma_sep print_static_typed_ident node_params)
    (print_list par comma_sep print_typed_ident node_inputs)
    (binop_sep "=")
    (print_list par comma_sep print_typed_ident node_outputs)
    (print_block !!node_body)

let print_const const_desc =
  dprintf "@[<hv 2>const %t%t%t@]"
    (print_ident const_desc.const_left)
    (binop_sep "=")
    (print_sexp const_desc.const_right)

let print_program prog =
  dprintf "@[<v>%t%t%t%t%t@]@."
    (print_list_naked dprint_newline print_enum prog.p_enums)
    ( match prog.p_enums, prog.p_consts with
      | [], _ | _, [] -> dprint_nop
      | _             -> dprint_newline
    )
    (print_list_naked dprint_newline print_const prog.p_consts)
    ( match prog.p_consts, prog.p_nodes with
      | [], _ | _, [] -> dprint_nop
      | _             -> dprint_newline
    )
    (print_list_naked dprint_newline print_node prog.p_nodes)

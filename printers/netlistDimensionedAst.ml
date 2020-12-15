open Format
open CommonAST
open CommonAst
open StaticTypedPartialAst
open NetlistDimensionedAST


(* Netlist expressions *)

let rec print_type = function
  | StaticTypedAST.TNDim opt_sint_l ->
      print_list brak comma_sep print_opt_int_exp opt_sint_l
  | StaticTypedAST.TProd l ->
      print_list par star_sep print_type l

let rec print_dim = function
  | NDim n ->
      dprintf "%id" n
  | NProd l ->
      print_list par star_sep print_dim l


let rec print_exp_desc = function
  | EConst v -> ParserAst.print_val v
  | EVar id  -> print_ident id
  | EReg e   -> dprintf "reg@,%t" (print_exp e)
  | ECall (fname, params, args) ->
      dprintf "%t@[<hv4>%t@,%t@]"
        (print_ident fname)
        (print_list_if_nonempty chev comma_sep print_unknown_exp params)
        (print_list par comma_sep print_exp args)
  | EMem (memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t,%t>(%t)"
        (print_mem_kind memkind)
        (print_opt_int_exp addr_size)
        (print_opt_int_exp word_size)
        (print_list_naked comma_sep print_exp args)

and print_exp exp =
  par (dprintf "%t: %t"
    (print_exp_desc exp.dim_desc)
    (print_dim exp.dim_nb))

let rec print_lval_desc lval_desc =
  match lval_desc with
  | LValDrop    -> dprintf "_"
  | LValId id   -> print_ident id
  | LValTuple l -> print_list par comma_sep print_lval l

and print_lval lval =
  par (dprintf "%t: %t"
    (print_lval_desc lval.dim_desc)
    (print_dim lval.dim_nb))

let print_eq_desc eq_desc =
  dprintf "@[<hv2>%t%t%t@]"
    (print_lval eq_desc.eq_left)
    (binop_sep "=")
    (print_exp eq_desc.eq_right)

let print_eq eq = print_eq_desc eq.desc

let is_bit tid_desc =
  match tid_desc.typed.desc with
  | TNDim [] -> true
  | TNDim _ -> false
  | TProd _ -> false

let print_tid_desc tid_desc =
  dprintf "@[<hv2>%t%t@]"
    (print_ident tid_desc.name)
    (dprint_if (not (is_bit tid_desc)) @@
      dprintf ":%t"
        (print_type tid_desc.typed.desc)
    )

let print_tid tid = print_tid_desc tid.desc

let rec print_block_desc block_desc =
  match block_desc with
  | BEqs l -> print_list_naked semicolon_sep print_eq l.equations
  | BIf (se, b1, b2) ->
      dprintf "@[if@ %t@ then@]@;<1 2>@[<v>%t@]@ else@;<1 2>@[<v>%t@]@ end if"
        (print_bool_exp se)
        (print_block b1)
        (print_block b2)

and print_block block = print_block_desc block.desc

let print_node (node_name, node_desc) =
  dprintf "@[<v 2>@[<2>%t%s%t@,%t%t%t@;<1 -2>@]where@ %t@]@ end where"
    (print_inline_status node_desc.node_inline)
    node_name
    (print_list_if_nonempty chev comma_sep print_stid node_desc.node_params)
    (print_list par comma_sep print_tid node_desc.node_inputs)
    (binop_sep "=")
    (print_list par comma_sep print_tid node_desc.node_outputs)
    (print_block node_desc.node_body)


let print_program prog =
  let consts_list = List.map (fun nam -> nam, Env.find nam prog.p_consts) prog.p_consts_order in
  let nodes_list = List.of_seq @@ Env.to_seq prog.p_nodes in

  dprintf "@[<v>%t%t%t@]@."
    (print_list_naked dprint_newline print_const consts_list)
    ( match consts_list, nodes_list with
      | [], _ | _, [] -> dprint_nop
      | _             -> dprint_newline
    )
    (print_list_naked dprint_newline print_node nodes_list)

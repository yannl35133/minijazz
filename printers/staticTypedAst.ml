open Format
open CommonAST
open CommonAst
open StaticTypedPartialAst
open StaticTypedAST

let print_slice_param = function
  | SliceAll   ->     dprintf ".."
  | SliceOne x ->     dprintf "%t"   (print_opt_int_exp x)
  | SliceTo hi ->     dprintf "..%t" (print_opt_int_exp hi)
  | SliceFrom lo ->   dprintf "%t.." (print_opt_int_exp lo)
  | Slice (lo, hi) -> dprintf "%t..%t" (print_opt_int_exp lo) (print_opt_int_exp hi)

(* Netlist expressions *)

let rec print_type = function
  | StaticTypedAST.TNDim opt_sint_l ->
      print_list brak comma_sep print_opt_int_exp opt_sint_l
  | StaticTypedAST.TProd l ->
      print_list par star_sep print_type l


let rec print_exp_desc = function
  | EConst v -> ParserAst.print_val v
  | EConstr (Estate0 c) -> print_ident c
  | EConstr (Estaten (c, es)) ->
      dprintf "%t@ (%t)"
        (print_ident c)
        (print_list_naked comma_sep print_exp es)
  | EVar id  -> print_ident id
  | EReg e   -> dprintf "reg@,%t" (print_exp e)
  | ESlice (params, arg) ->
    dprintf "%t%t"
      (print_exp arg)
      (print_list brak comma_sep print_slice_param params)
  | ESupOp (op, args) when !!op = "not" ->
      dprintf "%t%t"
        (print_ident op)
        (print_list par comma_sep print_exp args)
  | ESupOp (op, args) when !!op = "mux" ->
      dprintf "%t%t"
        (print_ident op)
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
        (print_ident fname)
        (print_list_if_nonempty chev comma_sep print_unknown_exp params)
        (print_list par comma_sep print_exp args)
  | EMem (memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t,%t>(%t)"
        (print_mem_kind memkind)
        (print_opt_int_exp addr_size)
        (print_opt_int_exp word_size)
        (print_list_naked comma_sep print_exp args)
  | ELet (eq, exp) ->
      dprintf "let %t@ =@ %t"
        (print_eq eq)
        (print_exp exp)
  | EMerge _ -> assert false

and print_exp exp = print_exp_desc exp.desc

and print_lval_desc lval_desc =
  match lval_desc with
  | ParserAST.LValDrop    -> dprintf "_"
  | ParserAST.LValId id   -> print_ident id
  | ParserAST.LValTuple l -> print_list par comma_sep print_lval l

and print_lval lval = print_lval_desc lval.desc

and print_automaton_hdl hdl =
  ParserAST.(
    dprintf "%t -> do %t"
      (state_name hdl.s_state |> print_ident)
      (print_eq hdl.s_body)
  )

and print_eq_desc = function
  | EQempty -> fun _ -> ()
  | EQeq (lv, exp) ->
      dprintf "@[<h>%t%t%t@]"
        (print_lval lv)
        (binop_sep "=")
        (print_exp exp)
  | EQand eqs ->
      print_list_naked and_sep print_eq eqs
  | EQlet (eq, eq') ->
      dprintf "let %t in@ %t"
        (print_eq eq)
        (print_eq eq')
  | EQreset (eq, exp) ->
      dprintf "reset %t@ every %t"
        (print_eq eq)
        (print_exp exp)
  | EQautomaton hdls ->
      print_list_naked bar_sep print_automaton_hdl hdls
  | EQmatch _ -> assert false

and print_eq eq = print_eq_desc eq.desc

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
  | BEqs l -> print_list_naked semicolon_sep print_eq l
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

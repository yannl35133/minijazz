open Format
open CommonAST
open CommonAst
open ParserAST

(* Static expression *)

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

let print_opt_sexp_desc = function
  | SExp se_desc -> print_sexp_desc se_desc
  | SUnknown _   -> dprint_nop

let print_opt_sexp opt_se = print_opt_sexp_desc opt_se.desc

let print_stid_desc stid_desc =
  dprintf "%t: %t"
    (print_ident stid_desc.st_name)
    (print_ident stid_desc.st_type_name)

let print_stid stid = print_stid_desc stid.desc

(* Netlist expressions *)

let rec print_type = function
  | TNDim opt_se_l ->
      print_list brak comma_sep print_opt_sexp opt_se_l
  | TProd l ->
      print_list par star_sep print_type l

let rec print_val = function
  | VNDim l ->
      dprintf "@[<hv>[%t]@]@,"
        (print_list_naked dprint_nop print_val l)
  | VBit b -> dprint_bool b


let infix_nodes = ["xor"; "and"; "or"]
let is_infix ident_desc =
   List.mem ident_desc infix_nodes


let print_slice_param = function
  | SliceAll   ->     dprintf ".."
  | SliceOne x ->     dprintf "%t"   (print_opt_sexp x)
  | SliceTo hi ->     dprintf "..%t" (print_opt_sexp hi)
  | SliceFrom lo ->   dprintf "%t.." (print_opt_sexp lo)
  | Slice (lo, hi) -> dprintf "%t..%t" (print_opt_sexp lo) (print_opt_sexp hi)

let rec print_exp_desc = function
  | EConst v -> print_val v
  | EConstr c -> print_ident c
  | EVar id  -> print_ident id
  | EPar e   -> par (print_exp e)
  | EReg e   -> dprintf "reg@,%t" (print_exp e)
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

and print_lval_desc lval_desc =
  match lval_desc with
  | LValDrop    -> dprintf "_"
  | LValId id   -> print_ident id
  | LValTuple l -> print_list par comma_sep print_lval l

and print_lval lval = print_lval_desc lval.desc

and print_automaton_hdl hdl =
  let kw, lst = if hdl.s_unless <> []
                then "unless", hdl.s_unless
                else "until", hdl.s_until in
  dprintf "| %t -> @[<v>do %t %s %t@]"
    (print_ident hdl.s_state)
    (print_decl hdl.s_body)
    kw
    (print_list_naked else_sep print_escape lst)


and print_escape esc =
  dprintf "@[%t kw %t in %t@]"
    (print_exp esc.e_cond)
    (print_decl esc.e_body)
    (print_ident esc.e_nx_state)

and print_decl_desc = function
  | Dempty -> fun _ -> ()
  | Deq (lv, exp) ->
      dprintf "@[<h>%t%t%t@]"
        (print_lval lv)
        (binop_sep "=")
        (print_exp exp)
  | Dblock eqs ->
      print_list_naked and_sep print_decl eqs
  | Dreset (eq, exp) ->
      dprintf "reset %t@ every %t"
        (print_decl eq)
        (print_exp exp)
  | Dautomaton hdls ->
     dprintf "automaton@ @[<v>%t@]@ end"
      (print_list_naked newline_sep print_automaton_hdl hdls)
  | Dmatch _ -> assert false
  | Dif (se, b1, b2) ->
     dprintf "@[if@ %t@ then@]@;<1 2>@[<v>%t@]@ else@;<1 2>@[<v>%t@]@ end if"
        (print_sexp se)
        (print_decl b1)
        (print_decl b2)

and print_decl eq = print_decl_desc eq.desc

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

let print_node_desc node_desc =
  dprintf "@[<v 2>@[<2>%t%t%t@,%t%t%t@;<1 -2>@]where@ %t@]@ end where"
    (print_inline_status node_desc.node_inline)
    (print_ident node_desc.node_name)
    (print_list_if_nonempty chev comma_sep print_stid node_desc.node_params)
    (print_list par comma_sep print_tid node_desc.node_inputs)
    (binop_sep "=")
    (print_list par comma_sep print_tid node_desc.node_outputs)
    (print_decl node_desc.node_body)

let print_node node = print_node_desc node.desc

let print_const_desc const_desc =
  dprintf "@[<hv 2>const %t%t%t@]"
    (print_ident const_desc.const_left)
    (binop_sep "=")
    (print_sexp const_desc.const_right)

let print_const const = print_const_desc const.desc

let print_program prog =
  dprintf "@[<v>%t%t%t@]@."
    (print_list_naked dprint_newline print_const prog.p_consts)
    ( match prog.p_consts, prog.p_nodes with
      | [], _ | _, [] -> dprint_nop
      | _             -> dprint_newline
    )
    (print_list_naked dprint_newline print_node prog.p_nodes)

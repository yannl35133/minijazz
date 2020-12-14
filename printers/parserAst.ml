open Format
open CommonAST
open ParserAST

(* Helpers *)

let dprint_string str ff = pp_print_string ff str
let dprint_int i ff = pp_print_int ff i
let dprint_bool b = dprint_string (if b then "1" else "0")
let dprint_concat printer1 printer2 (ff: formatter) = (printer1 ff) ; (printer2 ff)
let (@@) p1 p2 = (fun ff -> dprint_concat p1 p2 ff)
let nop (_: formatter) = ()

let dprint_break nspace ind ff = pp_print_break ff nspace ind
let dprint_cut ff = pp_print_cut ff ()
let dprint_space ff = pp_print_space ff ()

let dforce_newline ff = pp_force_newline ff ()
let dforce_linejump = dforce_newline @@ dforce_newline

let rec dprint_list sep printer l =
  match l with
  | []     -> nop
  | [h]    -> printer h
  | h :: t -> (printer h) @@ sep @@ (dprint_list sep printer t)

let if_empty_list_dprint l printer =
  match l with
  | [] -> nop
  | _  -> printer

let dprint_if b printer = if b then printer else nop
let dprint_newline ff = pp_print_newline ff ()

let dbox i printer ff = (open_hvbox (2 * i) ; printer ff ; close_box ())
let dvbox i printer ff = (open_vbox (2 * i) ; printer ff ; close_box ())

let binop_sep str = dprintf " %s@ " str
let star_sep = binop_sep "*"
let comma_sep = dprintf ",@ "
let semicolon_sep = dprintf ";@ "
let and_sep = dprintf "and "
let bar_sep = dprintf "|@ "

let delim prefix printer suffix =
  dbox 1 (
    prefix @@ dprint_cut @@
    printer @@
    dprint_break 0 (-2) @@
    suffix
  )

let par printer = delim (dprint_string "(") printer (dprint_string ")")
let mark printer = delim (dprint_string "<") printer (dprint_string ">")
let bracket printer = delim (dprint_string "[") printer (dprint_string "]")


(* Static expression *)

let print_sop sop =
  let op_str =
    match sop with
    | SAdd -> "+" | SMinus -> "-" | SMult -> "*" | SDiv -> "/" | SPower -> "^"
    | SEq -> "=" | SNeq -> "!="
    | SLt -> "<" | SLeq -> "<=" | SGt -> ">" | SGeq -> ">="
    | SOr -> "||" | SAnd -> "&&"
  in
  binop_sep op_str

let print_sunop unop =
  let op_str =
    match unop with
    | SNeg -> "-"
    | SNot -> "!"
  in
  dprint_string op_str

let rec print_sexp_desc = function
  | SInt i    -> dprint_int i
  | SBool b   -> dprint_bool b
  | SIdent id -> Ident.dprint_ident id
  | SPar se   -> par (print_sexp se)
  | SUnOp (sunop, se) -> print_sunop sunop @@ print_sexp se
  | SBinOp (sop, se1, se2) -> print_sexp se1 @@ print_sop sop @@ print_sexp se2
  | SIf (c, se1, se2) ->
      dbox 1 (
        dprintf "%t ?@ %t@ : %t"
          (print_sexp c)
          (print_sexp se1)
          (print_sexp se2)
      )

and print_sexp se = print_sexp_desc se.desc

let print_opt_sexp_desc opt_se_desc =
  match opt_se_desc with
  | Some se_desc -> print_sexp_desc se_desc
  | None         -> nop

let print_opt_sexp opt_se = print_opt_sexp_desc opt_se.desc

let print_stid stid =
  dprintf "%t:%t"
    (Ident.dprint_ident stid.st_name)
    (dprint_string !!(stid.st_type_name))

(* Netlist expressions *)

let rec print_type = function
  | TNDim opt_se_l -> bracket (dprint_list comma_sep print_opt_sexp opt_se_l )
  | TProd l -> par (dprint_list star_sep print_type l)

let rec print_val = function
  | VNDim l ->
      dprintf "@[<hv>[%t]@]@ " (dprint_list nop print_val l)
  | VBit b -> dprint_bool b

let print_mem_kind_desc mem_kind_desc =
  match mem_kind_desc with
  | MRom -> dprint_string "rom"
  | MRam -> dprint_string "ram"

let print_mem_kind mem_kind = print_mem_kind_desc mem_kind.desc

let infix_nodes = ["xor"; "and"; "or"]
let is_infix ident_desc =
   List.mem ident_desc infix_nodes

let slice_nodes = ["slice"; "slice_from"; "slice_to"]
let is_slice ident_desc =
  List.mem ident_desc slice_nodes

let print_slice_param = function
  | SliceAll   ->     dprintf ".."
  | SliceOne x ->     dprintf "%t" (print_opt_sexp x)
  | SliceTo hi ->     dprintf "..%t" (print_opt_sexp hi)
  | SliceFrom lo ->   dprintf "%t.." (print_opt_sexp lo)
  | Slice (lo, hi) -> dprintf "%t..%t" (print_opt_sexp lo) (print_opt_sexp hi)

let rec print_exp_desc = function
  | EConst v -> print_val v
  | EConstr (Estate0 c) -> Ident.dprint_ident c
  | EConstr (Estaten (c, es)) ->
     dprintf "%t@ (%t)" (Ident.dprint_ident c)
       ((dprint_list comma_sep print_exp) es)
  | EVar id  -> Ident.dprint_ident id
  | EPar e   -> par (print_exp e)
  | EReg e   -> dprintf "reg@ %t" (print_exp e)
  | ESlice (params, arg) ->
      dprintf "%t[%t]" (print_exp arg) (dprint_list (dprintf ",") print_slice_param params)
  | ESupOp (op, args) when !!op = "not" ->
      dprintf "@[<2>%t%t@]" (dprint_string !!op) (par ((dprint_list comma_sep print_exp) args))
  | ESupOp (op, args) ->
      let e1, e2 = Misc.assert_2 args in
      dprintf "@[<2>%t %t@ %t@]" (print_exp e1) (dprint_string !!op) (print_exp e2)
  | ECall (ident, _, args) when ident.i_name = "concat" ->
      let e1, e2 = Misc.assert_2 args in
      dprintf "%t . %t" (print_exp e1) (print_exp e2)
  | ECall (ident, params, args) ->
      dbox 2 (
        Ident.dprint_ident ident @@
        if_empty_list_dprint params
          (mark ((dprint_list comma_sep print_opt_sexp) params)) @@
        par ((dprint_list comma_sep print_exp) args)
      )
  | EMem (memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t,%t>(%t)"
        (print_mem_kind memkind)
        (print_opt_sexp addr_size)
        (print_opt_sexp word_size)
        ((dprint_list comma_sep print_exp) args)
  | ELet (eq, exp) ->
     dprintf "let %t@ =@ %t" (print_decl eq) (print_exp exp)
  | EMerge _ -> assert false
  | EMatch _ -> assert false

and print_exp exp fmt = print_exp_desc exp.desc fmt

and print_lval_desc lval_desc =
  match lval_desc with
  | LValDrop    -> dprint_string "_"
  | LValId id   -> Ident.dprint_ident id
  | LValTuple l -> dprint_list comma_sep print_lval l

and print_lval lval = print_lval_desc lval.desc

and print_automaton_hdl hdl =
  dprintf "%t -> do %t"
    (state_name hdl.s_state |> Ident.dprint_ident)
    (print_decl hdl.s_body)

and print_decl_desc = function
  | Dempty -> fun _ -> ()
  | Deq (lv, exp) ->
     dprintf "@[<1>%t@ =@ %t@]" (print_lval lv) (print_exp exp)
  | Dand eqs -> dprint_list semicolon_sep print_decl eqs
  | Dlet (eq, eq') ->
     dprintf "@[<1>let %t in %t@]" (print_decl eq) (print_decl eq')
  | Dreset (eq, exp) ->
     dprintf "@[<1>reset %t every %t@]" (print_decl eq) (print_exp exp)
  | Dautomaton hdls -> dprint_list bar_sep print_automaton_hdl hdls
  | Dif (se, b1, b2) ->
       dbox 0 (
        dbox 0 (
          dprint_string "if" @@ dprint_space @@
          print_sexp se @@ dprint_space @@
          dprint_string "then"
        ) @@ dprint_break 1 2 @@
        dbox 0 (print_decl b1) @@ dprint_space @@
        dprint_string "else" @@ dprint_break 1 2 @@
        dbox 0 (print_decl b2)
      )
and print_decl eq = print_decl_desc eq.desc

let is_bit tid_desc =
  match tid_desc.typed.desc with
  | TProd _ -> false
  | TNDim [] -> true
  | TNDim _ -> false

let print_tid tid =
  dbox 1 (
    Ident.dprint_ident tid.name @@
    dprint_if (not (is_bit tid))
    (dprintf ":@," @@ print_type tid.typed.desc)
  )

let print_inline_status inline_status =
  match inline_status with
  | Inline    -> dprint_string "inline "
  | NotInline -> nop

let print_node node =
  dvbox 1 (
    dbox 1 (
      print_inline_status node.node_inline @@
      Ident.dprint_ident node.node_name @@
      if_empty_list_dprint node.node_params
        (mark (dprint_list comma_sep print_stid node.node_params)) @@
      dprint_cut @@
      par (dprint_list comma_sep print_tid node.node_inputs) @@
      binop_sep "=" @@
      par (dprint_list comma_sep print_tid node.node_outputs) @@
      dprint_break 1 (-2)
    ) @@
    dprint_string "where" @@
    dprint_space @@
    print_decl node.node_body
  ) @@
  dprint_space @@
  dprint_string "end where"

let print_const const =
  dbox 1 (
    dprint_string "const " @@
    Ident.dprint_ident const.const_left @@
    binop_sep "=" @@
    print_sexp const.const_right
  )

let print_enum (e: enum) =
  dprintf "@[<1>enum %s@ (%t)]"
    e.enum_name.i_name
    (dprint_list comma_sep Ident.dprint_ident e.enum_pats)

let print_program prog =
  dprint_list dforce_newline print_const prog.p_consts @@
  (
    match prog.p_consts, prog.p_nodes with
    | [], _ | _, [] -> nop
    | _             -> dforce_linejump
  ) @@
  dprint_list dforce_linejump print_node prog.p_nodes @@
  dprint_newline
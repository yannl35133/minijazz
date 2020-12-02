open Format
open ParserAST
open CommonAST

(* Helpers *)

let dprint_string str ff = pp_print_string ff str
let dprint_int i ff = pp_print_int ff i
let dprint_bool b = dprint_string (if b then "1" else "0")
let dprint_concat printer1 printer2 ff = (printer1 ff) ; (printer2 ff)
let (@@) p1 p2 = (fun ff -> dprint_concat p1 p2 ff)
let nop _ = ()

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

let dbox i printer ff = (open_hvbox (2 * i) ; printer ff ; close_box ())
let dvbox i printer ff = (open_vbox (2 * i) ; printer ff ; close_box ())

let binop_sep str = dprintf " %s@ " str
let star_sep = binop_sep "*"
let comma_sep = dprintf ",@ "
let semicolon_sep = dprintf ";@ "

let delim prefix printer suffix =
  dbox 1 (
    prefix @@
    printer @@
    dprint_break 0 (-2) @@
    suffix
  )

let par printer = delim (dprint_string "(") printer (dprint_string ")")
let mark printer = delim (dprint_string "<") printer (dprint_string ">")
let bracket printer = delim (dprint_string "[") printer (dprint_string "]")

(* Commons *)

let print_ident id = dprint_string id.desc

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

let rec print_sexp_desc se_desc =
  match se_desc with
  | SInt i    -> dprint_int i
  | SBool b   -> dprint_bool b
  | SIdent id -> print_ident id
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

let print_stid_desc stid_desc =
  dprintf "%t : %t" 
    (print_ident stid_desc.st_name)
    (print_ident stid_desc.st_type_name)

let print_stid stid = print_stid_desc stid.desc

(* Netlist expressions *)

let rec print_type typ =
  match typ with
  | TBitArray opt_se -> bracket (print_opt_sexp opt_se )
  | TProd l -> par (dprint_list star_sep print_type l)

let print_val v =
  match v with
  | VBitArray arr ->
      dprintf "[%t]" (dprint_list nop dprint_bool (Array.to_list arr))

let print_mem_kind_desc mem_kind_desc =
  match mem_kind_desc with
  | MRom -> dprint_string "rom"
  | MRam -> dprint_string "ram"

let print_mem_kind mem_kind = print_mem_kind_desc mem_kind.desc

let rec print_exp_desc exp_desc =
  match exp_desc with
  | EConst v -> print_val v
  | EVar id  -> print_ident id
  | EPar e   -> par (print_exp e)
  | EReg e   -> dprintf "reg@ %t" (print_exp e)
  | ECall(ident, idx::_, args) when ident.desc = "select" ->
      let e1 = Misc.assert_1 args in
      dprintf "%t[%t]" (print_exp e1) (print_opt_sexp idx)
  | ECall(ident, low::high::_, args) when ident.desc = "slice" ->
      let e1 = Misc.assert_1 args in
      dprintf "%t[%t..%t]"
        (print_exp e1)
        (print_opt_sexp low)
        (print_opt_sexp high)
  | ECall(ident, _, args) when ident.desc = "concat" ->
      let e1, e2 = Misc.assert_2 args in
      dprintf "%t . %t" (print_exp e1) (print_exp e2)
  | ECall(ident, params, args) ->
      dbox 2 (
        print_ident ident @@
        if_empty_list_dprint params 
          (mark ((dprint_list comma_sep print_opt_sexp) params)) @@
        par ((dprint_list comma_sep print_exp) args)
      )
  | EMem(memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t,%t>(%t)"
        (print_mem_kind memkind)
        (print_sexp addr_size)
        (print_sexp word_size)
        ((dprint_list comma_sep print_exp) args)

and print_exp exp = print_exp_desc exp.desc

let rec print_lval_desc lval_desc =
  match lval_desc with
  | LValDrop    -> dprint_string "_"
  | LValId id   -> print_ident id
  | LValTuple l -> dprint_list comma_sep print_lval l

and print_lval lval = print_lval_desc lval.desc

let print_eq_desc eq_desc =
  dbox 1 (
    print_lval eq_desc.eq_left @@
    binop_sep "=" @@
    print_exp eq_desc.eq_right
  )

let print_eq eq = print_eq_desc eq.desc

let print_tid_desc tid_desc =
  dbox 1 (
    print_ident tid_desc.name @@
    binop_sep ":" @@
    print_type tid_desc.typed.desc
  )

let print_tid tid = print_tid_desc tid.desc

let rec print_block_desc block_desc =
  match block_desc with
  | BEqs l -> dprint_list semicolon_sep print_eq l
  | BIf (se, b1, b2) -> 
      dbox 1 (
        dprintf "if@ %t@ "
        (print_sexp se)
      ) @@ 
      dbox 1 (
        dprintf "then@ %t@ else@ %t"
        (print_block b1)
        (print_block b2)
      )

and print_block block = print_block_desc block.desc

let print_inline_status inline_status =
  match inline_status with
  | Inline    -> dprint_string "inline "
  | NotInline -> nop

let print_node_desc node_desc =
  dvbox 1 (
    dbox 0 (
      print_inline_status node_desc.node_inline @@
      print_ident node_desc.node_name @@
      if_empty_list_dprint node_desc.node_params
        (mark (dprint_list comma_sep print_stid node_desc.node_params)) @@
      dprint_cut @@
      par (dprint_list comma_sep print_tid node_desc.node_inputs) @@
      binop_sep "=" @@
      par (dprint_list comma_sep print_tid node_desc.node_outputs) @@
      dprint_space
    ) @@
    dprint_string "where" @@
    dprint_space @@
    print_block node_desc.node_body
  ) @@
  dprint_space @@
  dprint_string "end where"

let print_node node = print_node_desc node.desc

let print_const_desc const_desc =
  dbox 1 (
    dprint_string "const " @@
    print_ident const_desc.const_left @@
    binop_sep "=" @@
    print_sexp const_desc.const_right
  )

let print_const const = print_const_desc const.desc
  
let print_program prog =
  dprint_list dforce_newline print_const prog.p_consts @@
  (
    match prog.p_consts, prog.p_nodes with
    | [], _ | _, [] -> nop
    | _             -> dforce_linejump
  ) @@
  dprint_list dforce_linejump print_node prog.p_nodes

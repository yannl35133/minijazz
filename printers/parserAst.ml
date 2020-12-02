open Format
open ParserAST
open CommonAST

(* Helpers *)

let star_sep ff () = fprintf ff " *@ "
let comma_sep ff () = fprintf ff ",@ "
let semicolon_sep ff () = fprintf ff ";@ "

(* Commons *)

let print_bool ff b =
  fprintf ff (if b then "1" else "0")

let print_ident ff id =
  fprintf ff "%s" id.desc

(* Static expression *)

let print_sop ff sop =
  let op_str = 
    match sop with
    | SAdd -> "+" | SMinus -> "-" | SMult -> "*" | SDiv -> "/" | SPower -> "^" 
    | SEq -> "=" | SNeq -> "!=" 
    | SLt -> "<" | SLeq -> "<=" | SGt -> ">" | SGeq -> ">="
    | SOr -> "||" | SAnd -> "&&"
  in
  pp_print_string ff op_str

let print_sunop ff unop =
  let op_str =
    match unop with
    | SNeg -> "-"
    | SNot -> "!"
  in
  pp_print_string ff op_str

let rec print_sexp_desc ff se_desc =
  match se_desc with
  | SInt i    -> pp_print_int ff i
  | SBool b   -> print_bool ff b
  | SIdent id -> print_ident ff id 
  | SPar se   -> fprintf ff "(%a)" print_sexp se
  | SUnOp (sunop, se) -> 
      fprintf ff "%a%a" print_sunop sunop print_sexp se
  | SBinOp (sop, se1, se2) -> 
      fprintf ff "%a %a %a" 
        print_sexp se1 
        print_sop sop 
        print_sexp se2
  | SIf (c, se1, se2) ->
      fprintf ff "%a @{<sif>?@} %a @{<sif>:@} %a"
        print_sexp c 
        print_sexp se1 
        print_sexp se2

and print_sexp ff se =
  print_sexp_desc ff se.desc

let print_opt_sexp_desc ff opt_se_desc =
  match opt_se_desc with
  | Some se_desc -> print_sexp_desc ff se_desc
  | None         -> ()

let print_opt_sexp ff opt_se =
  print_opt_sexp_desc ff opt_se.desc

let print_stid_desc ff stid_desc =
  fprintf ff "%a : %a" 
    print_ident stid_desc.st_name 
    print_ident stid_desc.st_type_name

let print_stid ff stid =
  print_stid_desc ff stid.desc

(* Netlist expressions *)

let rec print_type ff typ =
  match typ with
  | TBitArray opt_se -> fprintf ff "[%a]" print_opt_sexp opt_se 
  | TProd l -> 
      fprintf ff "(%a)" 
        (pp_print_list ~pp_sep:star_sep print_type) 
        l

let print_val ff v =
  match v with
  | VBitArray arr ->
      fprintf ff "[%a]"
        (pp_print_list print_bool)
        (Array.to_list arr)

let print_mem_kind ff mem_kind =
  match mem_kind.desc with
  | MRom -> fprintf ff "rom"
  | MRam -> fprintf ff "ram"

let rec print_exp_desc ff e_desc =
  match e_desc with
  | EConst v -> print_val ff v
  | EVar id  -> print_ident ff id
  | EPar e   -> fprintf ff "(%a)" print_exp e
  | EReg e   -> fprintf ff "reg@ %a" print_exp e 
  | ECall(ident, idx::_, args) when ident.desc = "select" ->
      let e1 = Misc.assert_1 args in
      fprintf ff "%a[%a]"
        print_exp e1
        print_opt_sexp idx
  | ECall(ident, low::high::_, args) when ident.desc = "slice" ->
      let e1 = Misc.assert_1 args in
      fprintf ff "%a[%a..%a]"
        print_exp e1
        print_opt_sexp low
        print_opt_sexp high
  | ECall(ident, _, args) when ident.desc = "concat" ->
      let e1, e2 = Misc.assert_2 args in
      fprintf ff "%a . %a"
        print_exp e1
        print_exp e2
  | ECall(ident, params, args) ->
      fprintf ff "%a@,<%a>@,(%a)" 
        print_ident ident
        (pp_print_list ~pp_sep:comma_sep print_opt_sexp) params
        (pp_print_list ~pp_sep:comma_sep print_exp) args
  | EMem(memkind, (addr_size, word_size, _), args) ->
      fprintf ff "%a<%a,%a>(%a)"
        print_mem_kind memkind
        print_sexp addr_size
        print_sexp word_size
        (pp_print_list ~pp_sep:comma_sep print_exp) args

and print_exp ff e =
  print_exp_desc ff e.desc

let rec print_lval_desc ff lval_desc =
  match lval_desc with
  | LValDrop    -> fprintf ff "_"
  | LValId id   -> print_ident ff id
  | LValTuple l -> pp_print_list ~pp_sep:comma_sep print_lval ff l

and print_lval ff lval =
  print_lval_desc ff lval.desc

let print_eq_desc ff eq_desc =
  fprintf ff "%a =@ %a"
    print_lval eq_desc.eq_left
    print_exp eq_desc.eq_right

let print_eq ff eq =
  print_eq_desc ff eq.desc

let print_tid_desc ff tid_desc =
  fprintf ff "%a : %a"
    print_ident tid_desc.name
    print_type tid_desc.typed.desc

let print_tid ff tid =
  print_tid_desc ff tid.desc

let rec print_block_desc ff block_desc =
  match block_desc with
  | BEqs l -> pp_print_list ~pp_sep:semicolon_sep print_eq ff l
  | BIf (se, b1, b2) -> 
      fprintf ff "if %a@ then@ %a@ else@ %a"
      print_sexp se
      print_block b1
      print_block b2

and print_block ff block =
  print_block_desc ff block.desc

let print_inline_status ff inline_status =
  match inline_status with
  | Inline    -> fprintf ff "inline "
  | NotInline -> ()

let print_node_desc ff node_desc =
  fprintf ff "%a%a<%a>(%a) = (%a) where@ %a@ end where"
    print_inline_status node_desc.node_inline
    print_ident node_desc.node_name
    (pp_print_list ~pp_sep:comma_sep print_stid) node_desc.node_params
    (pp_print_list ~pp_sep:comma_sep print_tid) node_desc.node_inputs
    (pp_print_list ~pp_sep:comma_sep print_tid) node_desc.node_outputs
    print_block node_desc.node_body
    (* print_constraints node_desc.n_constraints *)
    (* (pp_print_list ~pp_sep:comma_sep print_ident) node_desc.probes *)

let print_node ff node =
  print_node_desc ff node.desc

let print_const_desc ff const_desc =
  fprintf ff "const %a = %a"
    print_ident const_desc.const_left
    print_sexp const_desc.const_right

let print_const ff const =
  print_const_desc ff const.desc
  
let print_program ff prog =
  fprintf ff "%a@ %a"
    (pp_print_list print_const) prog.p_consts
    (pp_print_list print_node) prog.p_nodes

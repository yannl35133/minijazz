open Format
open CommonAST
open CommonAst
open StaticTypedPartialAst
open NetlistSizedAST


(* Netlist expressions *)
let print_size (Size e) = print_int_exp_desc e

let print_netlist_size = print_netlist_type print_size

let print_type = print_bitype print_netlist_size


let rec print_exp_desc = function
  | EConst v -> print_val v
  | EVar id  -> print_ident id
  | EReg e   -> dprintf "reg@ %t" (print_exp e)
  | ECall (fname, params, args) ->
      dprintf "%t@[<hv4>%t@,%t@]"
        (print_funname fname)
        (print_list_if_nonempty chev comma_sep print_bitype_exp params)
        (print_list par comma_sep print_exp args)
  | EMem (memkind, (addr_size, word_size, _), args) ->
      dprintf "%t<%t, %t>(%t)"
        (print_mem_kind memkind)
        (print_int_exp addr_size)
        (print_int_exp word_size)
        (print_list_naked comma_sep print_exp args)

and print_exp exp =
  par (dprintf "%t: %t"
    (print_exp_desc !$!exp)
    (print_netlist_size !$$exp))

let print_tritype_exp = print_tritype_exp print_exp

let print_lvalue = print_lvalue0 print_type

let rec print_decl_desc = function
  | Deq (lv, exp) ->
      dprintf "@[%t%t@;<1 4>%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_tritype_exp exp)
        (semicolon_sep)
  | Dlocaleq (lv, exp) ->
      dprintf "@[local %t%t@;<1 4>%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_tritype_exp exp)
        (semicolon_sep)
  | Dreset (exp, eqs) ->
      dprintf "@[<hv2>reset@ %t@]@ every %t%t"
        (print_block print_decl eqs)
        (print_exp exp)
        (semicolon_sep)
  | Dautomaton auto ->
     dprintf "@[<v2>automaton@ %t@]@ end"
      (print_automaton (print_exp, print_state_transition_exp print_exp, print_decl) auto)
  | Dmatch (e, matcher) ->
      dprintf "@[<v2>match %t with@ %t@]@ end"
        (print_state_exp print_exp e)
        (print_matcher print_decl matcher)
  | Dif (se, b1, b2) ->
     dprintf "@[if@ %t@ then@]@;<1 2>@[<v>%t@]@ else@;<1 2>@[<v>%t@]@ end if"
        (print_bool_exp se)
        (print_block print_decl b1)
        (print_block print_decl b2)

and print_decl eq = print_decl_desc eq.desc

let print_node n = print_node (print_static_type, print_size, print_decl) n
let print_program p = print_program (print_static_type, print_bitype_exp, print_size, print_decl) p

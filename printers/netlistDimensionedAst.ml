open Format
open CommonAST
open CommonAst
open StaticTypedPartialAst
open NetlistDimensionedAST


(* Netlist expressions *)
let print_size = print_opt_int_exp

let rec print_dim = function
  | NDim n ->
      dprintf "%id" n
  | NProd l ->
      print_list par star_sep print_dim l

let print_type = print_bitype print_dim


let rec print_exp_desc = function
  | EConst v -> print_val v
  | EVar id  -> print_ident id
  | EReg e   -> dprintf "reg@ %t" (print_exp e)
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

and print_exp exp =
  par (dprintf "%t: %t"
    (print_exp_desc !%!exp)
    (print_dim !%%exp))

let print_tritype_exp = print_tritype_exp print_exp

let print_lvalue = print_lvalue print_type

let rec print_decl_desc = function
  | Deq (lv, exp) ->
      dprintf "@[<h>%t%t%t@]%t"
        (print_lvalue lv)
        (binop_sep "=")
        (print_tritype_exp exp)
        (semicolon_sep)
  | Dlocaleq (lv, exp) ->
      dprintf "@[<h>local %t%t%t@]%t"
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
      (print_automaton (print_exp, print_state_transition_exp, print_decl) auto)
  | Dmatch (e, matcher) ->
      dprintf "@[<v2>match %t with@ %t@]@ end"
        (print_state_exp e)
        (print_matcher print_decl matcher)
  | Dif (se, b1, b2) ->
     dprintf "@[if@ %t@ then@]@;<1 2>@[<v>%t@]@ else@;<1 2>@[<v>%t@]@ end if"
        (print_bool_exp se)
        (print_block print_decl b1)
        (print_block print_decl b2)

and print_decl eq = print_decl_desc eq.desc

let print_node = print_node (print_static_type, print_size, print_decl)
let print_program = print_program (print_static_type, print_bitype_exp, print_size, print_decl)

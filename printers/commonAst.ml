open Format
open CommonAST

(* Helpers *)

let dprint_bool b = dprintf "%s" (if b then "1" else "0")
let dprint_nop = dprintf ""


let rec print_list_naked sep printer l =
  match l with
  | []     -> dprint_nop
  | [h]    -> printer h
  | h :: t ->
      dprintf "%t%t%t"
        (printer h)
        sep
        (print_list_naked sep printer t)

let print_list del sep printer l =
  del (print_list_naked sep printer l)

let print_list_if_nonempty del sep printer l =
  match l with
  | [] -> dprint_nop
  | _  -> print_list del sep printer l

let dprint_if b printer = if b then printer else dprint_nop
let dprint_opt printer = function
  | Some thing -> printer thing
  | None -> dprint_nop
let dprint_newline = dprintf "@ "


let binop_sep str = dprintf " %s@ " str
let star_sep = binop_sep "*"
let comma_sep = dprintf ",@ "
let semicolon_sep = dprintf ";@ "
let and_sep = dprintf "and@ "
let bar_sep = dprintf "@ | "
let newline_sep = dprintf "@ "
let else_sep = dprintf "@ else "

let delim prefix suffix printer =
  dprintf "@[<hv 2>%t@,%t@;<0 -2>%t@]"
    prefix
    printer
    suffix


let par  = delim (dprintf "(") (dprintf ")")
let chev = delim (dprintf "<") (dprintf ">")
let brak = delim (dprintf "[") (dprintf "]")


(* CommonAST *)

let print_ident_desc (id: ident_desc) = dprintf "%s" id

let print_localized printer (e: 'a localized) = dprintf "%t" (printer e.desc)

let print_identified printer (e: ('a, 'uid) identified) = dprintf "%t" (printer e.id_desc)

let print_ident (id: ident) = dprintf "%s" id.id_desc (* "%t" (print_ident_desc id) *)
let print_constructor (id: constructor) = dprintf "%s" id.id_desc (* "%t" (print_ident_desc id) *)

let print_full_enum { enum_name; enum_constructors_names; _ } =
  dprintf "type %t =@[<hv2>@ %t@]"
    (print_ident enum_name)
    (print_list_naked (dprintf " |@ ") print_constructor enum_constructors_names)

let print_enum_type { enum_name; _ } = print_ident enum_name


(* Static expressions *)

let print_static_opt printer = function
  | SExp se_desc -> printer se_desc
  | SUnknown _   -> dprint_nop

let print_static_typed_ident printer { sti_name; sti_type; _ } =
  dprintf "%t: %t"
    (print_ident_desc !*!sti_name)
    (printer !!sti_type)


(* Netlist / state types *)

let print_transition = function
  | Continue -> dprintf "continue"
  | Reset -> dprintf "reset"

let print_bitype print_netlist_type = function
  | BNetlist ti -> print_netlist_type ti
  | BState enum ->
      print_enum_type enum
  | BStateTransition enum ->
      dprintf "%t transition"
        (print_enum_type enum)

let rec print_netlist_type printer = function
  | TNDim size_lst ->
      print_list brak comma_sep printer size_lst
  | TProd l ->
      print_list par star_sep (print_netlist_type printer) l

(* Netlist expressions *)

let rec print_val = function
  | VNDim l ->
      dprintf "@[<hv>[%t]@]@,"
        (print_list_naked dprint_nop print_val l)
  | VBit b -> dprint_bool b

let print_funname fname =
  print_ident_desc !!fname

let print_slice_param size_printer = function
  | SliceAll   ->     dprintf ".."
  | SliceOne x ->     dprintf "%t"   (size_printer x)
  | SliceTo hi ->     dprintf "..%t" (size_printer hi)
  | SliceFrom lo ->   dprintf "%t.." (size_printer lo)
  | Slice (lo, hi) -> dprintf "%t..%t" (size_printer lo) (size_printer hi)

let is_bit ti_type =
  match !!ti_type with
  | BNetlist TNDim [] -> true
  | _ -> false


let print_typed_ident print_size { ti_name; ti_type; _ } =
  dprintf "@[<hv2>%t%t@]"
    (print_ident ti_name)
    (dprint_if (not (is_bit ti_type)) @@
      dprintf ":%t"
        (print_bitype (print_netlist_type print_size) !!ti_type))


let rec print_match_handler print_decl { m_state; m_body; _ } =
  dprintf "| %t ->@[<hv2>@ %t@]"
    (print_constructor m_state)
    (print_block print_decl m_body)

and print_matcher print_decl { m_handlers; _ } =
  print_list_naked
    dprint_newline
    (print_match_handler print_decl)
    (List.map snd @@ List.of_seq @@ ConstructEnv.to_seq m_handlers)

and print_usual_transition (print_exp1, print_exp2) =
  print_list_naked
    else_sep
    (fun (e1, e2) ->
      dprintf "%t then@[<2>@ %t@]"
        (print_exp1 e1)
        (print_exp2 e2))

and print_automaton_handler (print_exp1, print_exp2, print_decl) { a_state; a_body; a_weak_transition; a_strong_transition; _ } =
  dprintf "@[<hv2>| %t ->@ %t@ %t@ %t@]"
    (print_constructor a_state)
    (print_block print_decl a_body)
    (dprint_if (a_weak_transition <> [])
      (dprintf "@[<hv2>until@ %t@]"
        (print_usual_transition (print_exp1, print_exp2) a_weak_transition)))
    (dprint_if (a_strong_transition <> [])
      (dprintf "@[<hv2>unless@ %t@]"
        (print_usual_transition (print_exp1, print_exp2) a_strong_transition)))

and print_automaton (print_exp1, print_exp2, print_decl) { a_handlers; a_fst_state; _ } =
  let fst_state_data = Misc.option_get ~error:(Failure "print_automaton") @@ ConstructEnv.find_opt !**a_fst_state a_handlers in
  let no_fst_state = ConstructEnv.remove !**a_fst_state a_handlers in

  print_list_naked
    dprint_newline
    (print_automaton_handler (print_exp1, print_exp2, print_decl))
    (fst_state_data :: (List.map snd @@ List.of_seq @@ ConstructEnv.to_seq no_fst_state))


and print_block print_decl =
  print_list_naked dprint_newline print_decl


let print_inline_status = function
  | Inline    -> dprintf "inline "
  | NotInline -> dprint_nop

let print_mem_kind_desc = function
  | MRom -> dprintf "rom"
  | MRam -> dprintf "ram"

let print_mem_kind mem_kind = print_mem_kind_desc mem_kind.desc

let print_const printer { const_name; const_decl; _ } =
  dprintf "@[<hv 2>const %t%t%t@]"
    (print_ident const_name)
    (binop_sep "=")
    (printer const_decl)


let print_node (print_static_type, print_size, print_decl)
      { node_name; node_inline; node_inputs; node_outputs; node_params; node_body; _ } =
  dprintf "@[<v 2>@[<2>%t%t%t@,%t%t%t@;<1 -2>@]where@ %t@]@ end where"
    (print_inline_status node_inline)
    (print_funname node_name)
    (print_list_if_nonempty chev comma_sep (print_static_typed_ident print_static_type) node_params)
    (print_list par comma_sep (print_typed_ident print_size) node_inputs)
    (binop_sep "=")
    (print_list par comma_sep (print_typed_ident print_size) node_outputs)
    (print_block print_decl node_body)

let print_program (print_static_type, print_static_exp, print_size, print_decl) { p_enums; p_consts; p_nodes; _ } =
  let p_enums = p_enums
    |> ConstructEnv.to_seq
    |> List.of_seq
    |> List.map snd
    |> List.sort_uniq (fun a b -> UIDIdent.compare a.enum_name.id_uid b.enum_name.id_uid)
  in
  let p_consts = p_consts (* Warning: may become out of order *)
    |> Env.to_seq
    |> List.of_seq
    |> List.map snd
    |> List.sort_uniq (fun a b -> UIDIdent.compare a.const_name.id_uid b.const_name.id_uid)
  in
  let p_nodes = p_nodes
  |> FunEnv.to_seq
  |> List.of_seq
  |> List.map snd
  in
  dprintf "@[<v>%t%t%t%t%t@]@."
    (print_list_naked dprint_newline print_full_enum p_enums)
    ( match p_enums, p_consts with
      | [], _ | _, [] -> dprint_nop
      | _             -> dprint_newline
    )
    (print_list_naked dprint_newline (print_const print_static_exp) p_consts)
    ( match p_consts, p_nodes with
      | [], _ | _, [] -> dprint_nop
      | _             -> dprint_newline
    )
    (print_list_naked dprint_newline (print_node (print_static_type, print_size, print_decl)) p_nodes)

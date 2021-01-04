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
let dprint_newline = dprintf "@ "


let binop_sep str = dprintf " %s@ " str
let star_sep = binop_sep "*"
let comma_sep = dprintf ",@ "
let semicolon_sep = dprintf ";@ "
let and_sep = dprintf "and@ "
let bar_sep = dprintf "|@ "

let delim prefix suffix printer =
  dprintf "@[<hv 2>%t@,%t@;<0 -2>%t@]"
    prefix
    printer
    suffix


let par  = delim (dprintf "(") (dprintf ")")
let chev = delim (dprintf "<") (dprintf ">")
let brak = delim (dprintf "[") (dprintf "]")


(* CommonAST *)

let print_ident (id: ident) = dprintf "%s" id.desc

let print_mem_kind_desc = function
  | MRom -> dprintf "rom"
  | MRam -> dprintf "ram"

let print_mem_kind mem_kind = print_mem_kind_desc mem_kind.desc

let print_inline_status = function
  | Inline    -> dprintf "inline "
  | NotInline -> dprint_nop

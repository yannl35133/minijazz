(***********************************************************************)
(*                                                                     *)
(*                             MiniJazz                                *)
(*                                                                     *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(*                                                                     *)
(* Copyright 2013 ENS                                                  *)
(*                                                                     *)
(* This file is part of the MiniJazz compiler.                         *)
(*                                                                     *)
(* MiniJazz is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* MiniJazz is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with MiniJazz.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

%{

open CommonAST
open ParserAST

let const_of_int loc i =
  let r =
    if fst i > 0 then
      Misc.bool_list_of_int i
    else
      try
        Misc.bool_list_of_dec_int i
      with Invalid_argument _ -> raise (Errors.Lexical_error (Errors.Nonbinary_base, loc))
  in
  match r with
      | [b] -> VBit b
      | l -> VNDim (List.map (fun b -> VBit b) l)


%}

%token CONST INLINE WHERE END PROBING
%token TYPE MATCH WITH AUTOMATON LOCAL RESET EVERY /* LET IN */ UNLESS UNTIL CONTINUE RESTART /* DO DONE */
%token ROM RAM REG MUX
%token IF THEN ELSE
%token ARROW "->"
%token LANGLE "<" RANGLE ">" LBRACKET "[" RBRACKET "]" LPAREN "(" RPAREN ")"
%token COLON ":" SEMICOL ";" COMMA "," EQUAL "=" DOT "." DOTDOT ".." BAR "|"
%token OR AND XOR NOR NAND NOT
%token PLUS "+" MINUS "-" STAR "*" SLASH "/" CIRCUMFLEX "^"
%token LEQ "<=" GEQ ">=" NEQ "<>"
%token WILDCARD "_" EOF
%token <string> IDENT
%token <string> CONSTRUCTOR
%token <string> STRING
%token <int * int> INT
%token <bool> BOOL

%nonassoc ELSE
%left LEQ GEQ EQUAL NEQ LANGLE RANGLE
%left DOT
%left OR NOR PLUS MINUS
%nonassoc RESTART CONTINUE
%left NAND XOR AND
%left STAR SLASH
%right NOT REG
%right CIRCUMFLEX

%start <ParserAST.program> program

%%

/** Tools **/
let slist  (x, sep) == separated_list (sep, x)
let snlist (x, sep) == separated_nonempty_list (sep, x)
let s2list (x, sep) == hd=x; sep; tl=separated_nonempty_list (sep, x); < (::) >
let stuple  (x, o, c) == o; ~=slist  (x, ","); c; <>
let sntuple (x, o, c) == o; ~=snlist (x, ","); c; <>
let tuple (x) == stuple(x, "(", ")")

let slist_optlast (x, sep) :=
  |                                       { [] }
  | ~=x;                                  { [x] }
  | ~=x; sep; ~=slist_optlast (x, sep);   < (::) >

let snlist_optlast (x, sep) :=
  | ~=x; sep?;                            { [x] }
  | ~=x; sep; ~=snlist_optlast (x, sep);  < (::) >

let localize (x) == ~=x; { localize $sloc x }
let ident == localize(IDENT)
let constructor == localize(CONSTRUCTOR)

// Enumerated type

let enum_constructor :=
  | BAR; constructor

let enum :=
  | TYPE; enum_name=ident; "="; enum_constructors=enum_constructor*;   { { enum_name; enum_constructors; enum_loc = Loc $sloc } }

// Static expressions

let static_value ==
  | ~=BOOL;     < SBool >
  | i=INT;      { SInt (snd i) }


let int_op ==
  | "+";  { SAdd }      | "-";  { SMinus }
  | "*";  { SMult }     | "/";  { SDiv }
  | "^";  { SPower }
let int_bool_op ==
  | "=";  { SEq }       | "<>"; { SNeq }
  | "<";  { SLt }       | "<="; { SLeq }
  | ">";  { SGt }       | ">="; { SGeq }
let bool_op ==
  | OR;   { SOr }       | AND;  { SAnd }

let int_unop ==
  | "-";  { SNeg }
let bool_unop ==
  | NOT;  { SNot }

let simple_static_exp == localize(simple_static_exp_desc)
let simple_static_exp_desc :=
  | static_value
  | ~=ident;                                                    < SIdent >
  | "("; ~=static_exp; ")";                                     < SPar >
  | unop=int_unop; se=simple_static_exp;                        { SUnOp (unop, se) }
  | se1=simple_static_exp; op=int_op; se2=simple_static_exp;    { SBinOp (op, se1, se2) }

let static_exp == localize(static_exp_desc)
let static_exp_desc :=
  | static_value
  | ~=ident;                                                    < SIdent >
  | "("; ~=static_exp; ")";                                     < SPar >
  | op=int_unop; se=static_exp;                                 { SUnOp (op, se) }
  | op=bool_unop;  se=static_exp;                               { SUnOp (op, se) }
  | se1=static_exp; op=int_op;      se2=static_exp;             { SBinOp (op, se1, se2) }
  | se1=static_exp; op=int_bool_op; se2=static_exp;             { SBinOp (op, se1, se2) }
  | se1=static_exp; op=bool_op;     se2=static_exp;             { SBinOp (op, se1, se2) }
  | IF; c=static_exp; THEN; se1=static_exp; ELSE; se2=static_exp; { SIf (c, se1 , se2) }

let opt_static_exp == localize(optional_static_exp_desc)
let optional_static_exp_desc :=
  | WILDCARD;                 { SUnknown (UIDUnknownStatic.get ()) }
  | ~=simple_static_exp_desc; < SExp >

let static_typed_ident :=
  | sti_name=ident;
      { { sti_name; sti_type = localize $sloc "int"; sti_loc = Loc $sloc } }
  | sti_name=ident; ":"; sti_type=ident;
      { { sti_name; sti_type; sti_loc = Loc $sloc } }

// Netlist expressions

let value :=
  | b=BOOL;                           { VBit b }
  | i=INT;                            { const_of_int (Loc $sloc) i }
  | "["; "]";                         { VNDim [] }
  | "["; ~=s2list(value, ","); "]";   < VNDim >

let slice_param :=
  | idx=opt_static_exp;                                                       < SliceOne >
  |                    "..";                                                  { SliceAll }
  | lo=opt_static_exp; "..";                                                  { SliceFrom lo }
  |                    ".."; hi=opt_static_exp;                               { SliceTo hi }
  | lo=opt_static_exp; ".."; hi=opt_static_exp;                               { Slice (lo, hi) }


let call_params :=
  | (* empty *)   { [] }
  | stuple(opt_static_exp, "<", ">")

let input_file :=
  | ","; STRING


let op == localize(_op)
let _op ==
  | "+";  { "or" }    | OR;   { "or" }
  | "*";  { "and" }   | AND;  { "and" }
  | "^";  { "xor" }   | XOR;  { "xor" }
  | NAND; { "nand" }  | NOR;  { "nor" }

let simple_exp == localize(simple_exp_desc)
let exp        == localize(exp_desc)
let simple_exp_desc :=
  | ~=ident;                                                                  < EVar >
  | ~=constructor;                                                            < EConstr >
  | "("; ~=exp; ")";                                                          < EPar >
let exp_desc :=
  | simple_exp_desc
  | ~=value;                                                                  < EConst >
  | CONTINUE; ~=exp;                                                          < EContinue >
  | RESTART; ~=exp;                                                           < ERestart >
  | REG; ~=exp;                                                               < EReg >
  | ~=ident; ~=call_params; ~=tuple(exp);                                     < ECall >
  | e1=exp; ~=op; e2=exp;                                                     { ESupOp (op, [e1; e2]) }
  | _m=MUX; e=tuple(exp);                                                     { ESupOp (localize $loc(_m) "mux", e) }
  | _n=NOT; e=exp;                                                            { ESupOp (localize $loc(_n) "not", [e])}
  | _b="["; e=exp; "]";                                                       { ESupOp (localize $loc(_b) "add_dim", [e])}
  | e1=exp; _c="."; e2=exp;                                                   { ESupOp (localize $loc(_c) "concat", [e1; e2]) }
  | e1=simple_exp; slice=sntuple(slice_param, "[", "]")+;                     { ESlice (List.flatten slice, e1) }
  | ro=rom_or_ram; "<"; addr_size=opt_static_exp; ",";
      word_size=opt_static_exp; input_file=input_file?; ">"; a=tuple(exp);    { EMem  (ro, (addr_size, word_size, input_file), a) }


let lvalue == localize(lvalue_desc)
let lvalue_desc :=
  | WILDCARD;         { LValDrop }
  | ~=ident;          < LValId >
  | ~=tuple(lvalue);  < LValTuple >

let typed_ident :=
  | ti_name=ident; { { ti_name; ti_loc = Loc $sloc; ti_type = localize $sloc (BNetlist (TNDim [])) } }
  | ti_name=ident; ":"; type_ident=sntuple(opt_static_exp, "[", "]")+;
    { { ti_name; ti_loc = Loc $sloc; ti_type = localize $loc(type_ident) (BNetlist (TNDim (List.flatten type_ident))) } }


// Automaton and state expressions

let state :=
  | c = constructor; { c }

let match_handler :=
  | BAR; m_state=state; ARROW; m_body=block;
        { { m_state; m_body; m_hloc = Loc $sloc } }

let matcher :=
  | MATCH; e=exp; WITH; m_handlers=match_handler*; END;
        { e, { m_handlers; m_loc = Loc $sloc } }

let escape :=
  | c = exp; THEN; e = exp;   { c, e }

let escape_list :=
  |                                                 { [], [] }
  | UNTIL;  l=snlist(escape, ELSE); r=escape_list;  { l @ fst r, snd r }
  | UNLESS; l=snlist(escape, ELSE); r=escape_list;  { fst r, l @ snd r }

let automaton_handler :=
  // | BAR; a_state = state; ARROW; a_body = block; DONE;
  //     { { a_state; a_body; a_weak_transition = []; a_strong_transition = [] } }
  | BAR; a_state = state; ARROW; a_body = block; THEN; e = exp;
      { { a_state; a_body; a_hloc = Loc $sloc; a_strong_transition = [];
          a_weak_transition = [localize $sloc (EConst (VBit true)), e] } }
  | BAR; a_state = state; ARROW; a_body = block; es = escape_list;
      { { a_state; a_body; a_hloc = Loc $sloc;
          a_weak_transition = fst es; a_strong_transition = snd es } }

let automaton :=
  | AUTOMATON; a_handlers=automaton_handler+; END;    { { a_handlers; a_loc = Loc $sloc; } }

let decl == localize(decl_desc)
let decl_desc :=
  | lv=lvalue; "="; e=exp;                  { Deq (lv, e) }
  | LOCAL; lv=lvalue; "="; e=exp;           { Dlocaleq (lv, e) }
  | RESET; eqs=block; EVERY; cond=exp;      { Dreset (cond, eqs) }
  | ~=automaton;                            < Dautomaton >
  | ~=matcher;                              < Dmatch >
  | IF; c=static_exp; THEN; b1=block;
    ELSE; b2=block; END; IF;      { Dif (c, b1, b2) }

let block := slist_optlast(decl, ";")


// Declarations (of equations and automata)

let node_inline :=
  |         { NotInline }
  | INLINE; { Inline }

let node_params :=
  | (* empty *)           { [] }
  | stuple(static_typed_ident, "<", ">")

let node_outputs :=
  | ~=typed_ident;      { [typed_ident] }
  | tuple(typed_ident)

let rom_or_ram == localize(_rom_or_ram)
let _rom_or_ram :=
  | ROM;    { MRom }
  | RAM;    { MRam }

probe_decls:
  | /*empty*/ { [] }
  | PROBING l=snlist(ident, ",") { l }



let node :=
  ~=node_inline; node_name=ident; ~=node_params;
    "("; node_inputs=slist(typed_ident, ","); ")"; "="; ~=node_outputs;
  WHERE; node_body=localize(block); node_probes=probe_decls; END; WHERE; ";"?;
    { { node_inline; node_name; node_params;
        node_inputs; node_outputs; node_body;
        node_probes; node_loc = Loc $sloc } }

let const :=
  | CONST; const_left=ident; "="; const_right=static_exp; ";"?;
      { { const_left; const_right; const_loc = Loc $sloc } }

let program :=
  | p_enums = enum*; p_consts = const*; p_nodes = node*; EOF;
      { { p_enums; p_consts; p_nodes } }


%%

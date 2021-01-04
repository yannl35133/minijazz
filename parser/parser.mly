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

%}

%token CONST INLINE WHERE END PROBING
%token AUTOMATON IN RESET EVERY LET UNLESS UNTIL CONTINUE DO DONE
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

%left LEQ GEQ EQUAL NEQ LANGLE RANGLE
%left DOT
%left OR NOR PLUS MINUS
%left NAND XOR AND
%left STAR SLASH
%right NOT REG
%right CIRCUMFLEX

%start <ParserAST.program> program

%%

/** Tools **/
let slist  (x, sep) == separated_list (sep, x)
let snlist (x, sep) == separated_nonempty_list (sep, x)
let stuple  (x, o, c) == o; ~=slist  (x, ","); c; <>
let sntuple (x, o, c) == o; ~=snlist (x, ","); c; <>
let tuple (x) == stuple(x, "(", ")")

let snlist_optlast (x, sep) :=
  | ~=x; sep?;                            { [x] }
  | ~=x; sep; ~=snlist_optlast (x, sep);  < (::) >

let localize (x) == ~=x; { localize $sloc x }
let ident == localize(IDENT)
let constructor == localize(CONSTRUCTOR)

let program :=
  | p_consts = list(const_decl); p_nodes = list(node_decl); EOF;
      { { p_consts; p_nodes } }

let const_decl == localize(const_decl_desc)
let const_decl_desc :=
  | CONST; const_left=ident; "="; const_right=static_exp; ";"?;
      { { const_left; const_right } }

let node_decl == localize(node_decl_desc)
let node_decl_desc :=
  ~=node_inline; node_name=ident; ~=node_params;
    "("; node_inputs=slist(typed_ident, ","); ")"; "="; ~=node_outputs;
  WHERE; node_body=block; node_probes=probe_decls; END; WHERE; ";"?;
      { { node_inline; node_name; node_params; node_inputs; node_outputs; node_body; node_probes } }

let node_inline :=
  |         { NotInline }
  | INLINE; { Inline }

let node_outputs :=
  | ~=typed_ident;      { [typed_ident] }
  | tuple(typed_ident)

let typed_ident == localize(typed_ident_desc)
let typed_ident_desc :=
  | name=ident; { { name; typed = localize $sloc (TNDim []) } }
  | name=ident; ":"; type_ident=sntuple(opt_static_exp, "[", "]")+;
    { { name; typed = localize $loc(type_ident) (TNDim (List.flatten type_ident)) } }

let opt_static_exp == localize(optional_static_exp_desc)
let optional_static_exp_desc :=
  | WILDCARD;                 { SUnknown (UniqueId.get ()) }
  | ~=simple_static_exp_desc; < SExp >

let node_params :=
  | (* empty *)           { [] }
  | stuple(node_param, "<", ">")

let node_param == localize(node_param_desc)
let node_param_desc :=
  | st_name=ident;
      { { st_name; st_type_name = localize $sloc "int" } }
  | st_name=ident; ":"; st_type_name=ident;
      { { st_name; st_type_name } }


let block == localize(block_desc)
let block_desc :=
  | ~=snlist_optlast (equation, ";");                           < BEqs >
  | IF; ~=static_exp; THEN; b1=block; ELSE; b2=block; END; IF;  < BIf >

let state :=
  | c = constructor; { Estate0 c }
  | c = constructor; LPAREN; es = snlist(exp, COMMA); RPAREN; { Estaten (c, es) }

let state_pat == localize(state_pat_desc)
let state_pat_desc :=
  | c = constructor; { Estate0pat c }
  | c = constructor; LPAREN; l = snlist(ident, COMMA); RPAREN;
    { Estatenpat (c, l) }

let decl :=
  | LET; v = ident; IN; d = decl; { let vs, eq = d in v :: vs, eq }
  | DO; eq = equation; { [], eq }

let emission :=
  | eq = equation; IN; s = state; { eq, s }
  | s = state; { localize $sloc EQempty, s }

let escape :=
  | c = exp; THEN; e = emission;
    { { e_cond = c; e_reset = true; e_body = fst e; e_nx_state = snd e } }
  | c = exp; CONTINUE; e = emission;
    { { e_cond = c; e_reset = true; e_body = fst e; e_nx_state = snd e } }

let escape_list := snlist(escape, ELSE)

let automaton_hdl :=
  | s_state = state_pat; ARROW; ds = decl; DONE;
    { let s_vars, s_body = ds in
      { s_state; s_body; s_vars; s_until = []; s_unless = [] } }
  | sp = state_pat; ARROW; ds = decl; THEN; e = emission;
    { { s_state = sp; s_vars = fst ds; s_body = snd ds;
        s_until = [{ e_cond = localize $sloc (EConst(VBit true));
                     e_reset = true; e_body = fst e;
                     e_nx_state = snd e }];
        s_unless = [] } }
  | sp = state_pat; ARROW; ds = decl; CONTINUE; e = emission;
    { let e_eqs, e_st = e in
      { s_state = sp; s_vars = fst ds; s_body = snd ds;
        s_until = [{ e_cond = localize $sloc (EConst(VBit true));
                     e_reset = false; e_body = e_eqs;
                     e_nx_state = e_st }];
        s_unless = [] } }
  | sp = state_pat; ARROW; ds = decl; UNTIL; es = escape_list;
    { { s_state = sp; s_vars = fst ds; s_body = snd ds;
        s_until = es; s_unless = [] } }
  | sp = state_pat; ARROW; ds = decl; UNLESS; es = escape_list;
    { { s_state = sp; s_vars = fst ds; s_body = snd ds;
        s_until = []; s_unless = es } }

let equation == localize(equation_desc)
let equation_desc :=
  | lv=lvalue; "="; e=exp; { EQeq (lv, e) }
(* | lst=snlist(equation, ";"); { EQand lst } *)
  | LET; e=equation; IN; e2=equation; { EQlet (e, e2) }
  | RESET; eq=equation; EVERY; e=exp; { EQreset (eq, e) }
  | AUTOMATON; lst=snlist(automaton_hdl, BAR); END; { EQautomaton lst }

let lvalue == localize(lvalue_desc)
let lvalue_desc :=
  | WILDCARD;         { LValDrop }
  | ~=ident;          < LValId >
  | ~=tuple(lvalue);  < LValTuple >

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


let simple_exp == localize(simple_exp_desc)
let exp        == localize(exp_desc)
let simple_exp_desc :=
  | ~=ident;                                                                  < EVar >
  | "("; ~=exp; ")";                                                          < EPar >
let exp_desc :=
  | simple_exp_desc
  | ~=const;                                                                  < EConst >
  | REG; ~=exp;                                                               < EReg >
  | ~=ident; ~=call_params; ~=tuple(exp);                                     < ECall >
  | e1=exp; ~=op; e2=exp;                                                     { ESupOp (op, [e1; e2]) }
  | _m=MUX; e=tuple(exp);                                                     { ESupOp (localize $loc(_m) "mux", e) }
  | _n=NOT; e=exp;                                                            { ESupOp (localize $loc(_n) "not", [e])}
  | _b="["; e=exp; "]";                                                       { ESupOp (localize $loc(_b) "add_dim", [e])}
  | e1=exp; _c="."; e2=exp;                                                   { ESupOp (localize $loc(_c) "concat", [e1; e2]) }
  | e1=simple_exp; slice=sntuple(slice_arg, "[", "]")+;                       { ESlice (List.flatten slice, e1) }
  | e1=simple_exp; idx=sntuple(opt_static_exp, "[", "]")+;                    { ESlice (List.map (fun e -> SliceOne e) (List.flatten idx), e1) }
  | ro=rom_or_ram; "<"; addr_size=opt_static_exp; ",";
      word_size=opt_static_exp; input_file=input_file?; ">"; a=tuple(exp);
                                                                              { EMem  (ro, (addr_size, word_size, input_file), a) }

let slice_arg :=
  |                    "..";                                                  { SliceAll }
  | lo=opt_static_exp; "..";                                                  { SliceFrom lo }
  |                    ".."; hi=opt_static_exp;                               { SliceTo hi }
  | lo=opt_static_exp; ".."; hi=opt_static_exp;                               { Slice (lo, hi) }

let op == localize(_op)
let _op ==
  | "+";  { "or" }    | OR;   { "or" }
  | "*";  { "and" }   | AND;  { "and" }
  | "^";  { "xor" }   | XOR;  { "xor" }
  | NAND; { "nand" }  | NOR;  { "nor" }

let const :=
  | b=BOOL;     { VBit b }
  | i=INT;
    {
      if fst i > 0 then
        let r = Misc.bool_list_of_int i in
        match r with
          | [b] -> VBit b
          | l -> VNDim (List.map (fun b -> VBit b) l)
      else begin
          let r =
            try
              Misc.bool_list_of_dec_int i
            with Invalid_argument _ -> raise (Errors.Lexical_error (Errors.Nonbinary_base, Loc $sloc))
          in
          match r with
            | [b] -> VBit b
            | l -> VNDim (List.map (fun b -> VBit b) l)
      end
    }
  | "["; "]";   { VNDim [] }

let rom_or_ram == localize(_rom_or_ram)
let _rom_or_ram :=
  | ROM;        { MRom }
  | RAM;        { MRam }

let input_file :=
  | ","; STRING

let call_params :=
  | (* empty *)   { [] }
  | stuple(opt_static_exp, "<", ">")

probe_decls:
  | /*empty*/ { [] }
  | PROBING l=snlist(ident, ",") { l }
%%

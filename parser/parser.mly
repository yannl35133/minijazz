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

open Ast_v2
open Location

let localize loc x = {
  desc = x;
  loc = Loc loc
}
let no_localize x = {
  desc = x;
  loc = no_location
}

%}

%token CONST INLINE WHERE END PROBING
%token ROM RAM REG
%token IF THEN ELSE
%token LANGLE "<" RANGLE ">" LBRACKET "[" RBRACKET "]" LPAREN "(" RPAREN ")"
%token SEMICOL ";" COMMA "," EQUAL "=" DOT "." DOTDOT ".."
%token OR AND XOR NOR NAND NOT
%token PLUS "+" MINUS "-" STAR "*" SLASH "/" CIRCUMFLEX "^"
%token LEQ "<=" GEQ ">=" NEQ "<>"
%token WILDCARD "_" EOF
%token <string> IDENT
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

%start <Ast_v2.program> program

%%

/** Tools **/
let slist  (x, sep)  == separated_list (sep, x)
let snlist (x, sep)  == separated_nonempty_list (sep, x)
let stuple (x, o, c) == o; ~=slist (x, ","); c; <>
let tuple (x) == stuple(x, "(", ")")

let localize (x) == ~=x; { localize $sloc x }

let program :=
  | p_consts = list(const_decl); p_nodes = list(node_decl); EOF;
      { { p_consts; p_nodes } }

let const_decl == localize(const_decl_desc)
let const_decl_desc :=
  | CONST; const_left=IDENT; "="; const_right=static_exp; ";"?;
      { { const_left; const_right } }

let node_decl == localize(node_decl_desc)
let node_decl_desc :=
  ~=node_inline; node_name=IDENT; ~=node_params;
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
  | name=IDENT; type_ident=type_ident?;
      { { name; typed = Option.value ~default:TBit type_ident } }

let type_ident ==
  | "["; ~=opt_static_exp; "]"; < TBitArray >

let opt_static_exp == localize(optional_static_exp_desc)
let optional_static_exp_desc :=
  | WILDCARD;             { None }
  | ~=simple_static_exp_desc;  < Some >

let node_params :=
  | (* empty *)     { [] }
  | stuple(IDENT, "<", ">")


let block == localize(block_desc)
let block_desc :=
  | ~=slist(equation, ";");                                    < BEqs >
  | IF; ~=static_exp; THEN; b1=block; ELSE; b2=block; END; IF; < BIf >

let equation == localize(equation_desc)
let equation_desc :=
  | eq_left=lvalue; "="; eq_right=exp; { { eq_left; eq_right } }

let lvalue == localize(lvalue_desc)
let lvalue_desc :=
  | WILDCARD;         { LValDrop }
  | ~=IDENT;          < LValId >
  | ~=tuple(lvalue);  < LValTuple >

let simple_static_exp == localize(simple_static_exp_desc)
let simple_static_exp_desc :=
  | i=INT;                                                      { SInt (snd i) }
  | ~=IDENT;                                                    < SConst >
  | "("; ~=static_exp; ")";                                     < SPar >
  | se1=simple_static_exp; op=int_op; se2=simple_static_exp;    { SBinOp (op, se1, se2) }

let static_exp == localize(static_exp_desc)
let static_exp_desc :=
  | static_value
  | ~=IDENT;                                      < SConst >
  | "("; ~=static_exp; ")";                       < SPar >
  | se1=static_exp; op=int_op;  se2=static_exp;   { SBinOp (op, se1, se2) }
  | se1=static_exp; op=bool_op; se2=static_exp;   { SBinOp (op, se1, se2) }

let static_value ==
  | ~=BOOL;     < SBool >
  | i=INT;      { SInt (snd i) }

let int_op ==
  | "+";  { SAdd }      | "-";  { SMinus }
  | "*";  { SMult }     | "/";  { SDiv }
  | "^";  { SPower }
let bool_op ==
  | "=";  { SEq }       | "<>"; { SNeq }
  | "<";  { SLt }       | "<="; { SLeq }
  | ">";  { SGt }       | ">="; { SGeq }
  | OR;   { SOr }       | AND;  { SAnd }


let simple_exp == localize(simple_exp_desc)
let exp        == localize(exp_desc)
let simple_exp_desc :=
  | ~=IDENT;                                                                  < EVar >
  | "("; ~=exp; ")";                                                          < EPar >
let exp_desc :=
  | simple_exp_desc
  | ~=const;                                                                  < EConst >
  | REG; ~=exp;                                                               < EReg >
  | ~=IDENT; ~=call_params; ~=tuple(exp);                                     < ECall >
  | e1=exp; ~=op; e2=exp;                                                     { ECall (op, [], [e1; e2]) }
  | NOT; e=exp;                                                               { ECall ("not", [], [e])}
  | e1=exp; "."; e2=exp;                                                      { ECall ("concat", [no_localize None; no_localize None], [e1; e2]) }
  | e1=simple_exp; "["; idx=opt_static_exp; "]";                              { ECall ("select", [no_localize None; idx], [e1]) }
  | e1=simple_exp; "["; low=opt_static_exp; ".."; high=opt_static_exp; "]";   { ECall ("slice",  [no_localize None; low; high], [e1]) }
  | e1=simple_exp; "["; low=opt_static_exp; ".."; "]";                        { ECall ("slice_from", [no_localize None; low], [e1]) }
  | e1=simple_exp; "["; ".."; high=opt_static_exp; "]";                       { ECall ("slice_to", [no_localize None; high], [e1]) }
  | ro=rom_or_ram; "<"; addr_size=simple_static_exp; ",";
      word_size=simple_static_exp; input_file=input_file?; ">"; a=tuple(exp);
                                                                              { EMem  (ro, addr_size, word_size, input_file, a) }

let op ==
  | "+";  { "or" }    | OR;   { "or" }
  | "*";  { "and" }   | AND;  { "and" }
  | "^";  { "xor" }   | XOR;  { "xor" }
  | NAND; { "nand" }  | NOR;  { "nor" }

let const :=
  | ~=BOOL;     < VBit >
  | i=INT;      { if fst i > 0 then VBitArray (Misc.bool_array_of_int i) else raise (Errors.Lexical_error (Nonbinary_base, Loc $sloc)) }
  | "["; "]";   { VBitArray (Array.make 0 false) }

let rom_or_ram :=
  | ROM;        { MRom }
  | RAM;        { MRam }

let input_file :=
  | ","; STRING

let call_params :=
  | (* empty *)   { [] }
  | stuple(opt_static_exp, "<", ">")

probe_decls:
  | /*empty*/ { [] }
  | PROBING l=snlist(IDENT, ",") { l }
%%

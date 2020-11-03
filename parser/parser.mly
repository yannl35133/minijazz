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

open Ident
open Static
open Ast
open Location
open Misc

let fresh_param () =
  mk_static_exp (SVar ("_n"^(Misc.gen_symbol ())))

%}

%token CONST INLINE WHERE END PROBING
%token ROM RAM REG
%token IF THEN ELSE
%token LANGLE "<" RANGLE ">" LBRACKET "[" RBRACKET "]" LPAREN "(" RPAREN ")"
%token SEMICOL ";" COLON ":" COMMA "," EQUAL "=" DOT "." DOTDOT ".."
%token OR AND XOR NAND NOT
%token PLUS MINUS STAR SLASH CIRCUMFLEX
%token LEQ
%token EOF
%token <string> IDENTIFIER
%token <string> STRING
%token <int * int> INT
%token <bool> BOOL

%left LEQ EQUAL
%left DOT
%left OR PLUS MINUS
%left NAND XOR AND
%left STAR SLASH
%right NOT REG
%right CIRCUMFLEX

%start program
%type <Ast.program> program

%%

/** Tools **/
%inline slist(x, S):      l = separated_list(S, x)             { l }
%inline snlist(x, S):     l = separated_nonempty_list(S, x)    { l }
%inline tuple(x):         "(" h = x "," t = snlist(x, ",") ")" { h :: t }
%inline tag_option(P, x):
  | /* empty */   { None }
  | P v = x       { Some v }

localize (x): y = x     { y, Loc $sloc }

program:
  | c = list(const_dec) n = list(node_dec) EOF
      { mk_program c n }

const_dec:
  | CONST id=IDENTIFIER "=" se=static_exp option(SEMICOL)
      { mk_const_dec ~loc:(Loc $sloc) id se }

node_dec:
  inline = inline  n = node_name
      p=params "(" args=slist(arg, ",") ")" "=" out=node_out
  WHERE b=block probes=probe_decls END WHERE option(";")
      { mk_node n (Loc $sloc) inline args out p b probes }

inline:
  |         { NotInline }
  | INLINE  { Inline }

node_name:
  | id=IDENTIFIER { reset_symbol_table (); id }

node_out:
  | a = arg                     { [a] }
  | "(" out=slist(arg, ",") ")" { out }

arg:
  | n=ident ":" t=type_ident { mk_var_dec n t }
  | n=ident                  { mk_var_dec n TBit }

ident:
  | id=IDENTIFIER { ident_of_string id }

type_ident: "[" se=static_exp "]" { TBitArray se }

params:
  | /*empty*/                     { [] }
  | "<" pl=snlist(param, ",") ">" { pl }

param:
  id=IDENTIFIER { mk_param id }


block:
  | eqs=equs { BEqs (eqs, []) }
  | IF se=static_exp THEN thenb=block ELSE elseb=block END IF { BIf(se, thenb, elseb) }

equs: eq=equ tl=equ_tail { eq::tl }
equ_tail:
  | /*empty*/ { [] }
  | SEMICOL { [] }
  | SEMICOL eq=equ tl=equ_tail { eq::tl }
equ: p=pat EQUAL e=exp { mk_equation p e }

pat:
  | n=ident                      { Evarpat n }
  | "(" p=snlist(ident, ",") ")" { Etuplepat p }

static_exp: se=_static_exp { mk_static_exp ~loc:(Loc $sloc) se }
_static_exp :
  | i=INT { SInt (snd i) }
  | id=IDENTIFIER { SVar id }
  | "(" se=_static_exp ")" { se }
  /*integer ops*/
  | se1=static_exp CIRCUMFLEX se2=static_exp { SBinOp(SPower, se1, se2) }
  | se1=static_exp PLUS se2=static_exp { SBinOp(SAdd, se1, se2) }
  | se1=static_exp MINUS se2=static_exp { SBinOp(SMinus, se1, se2) }
  | se1=static_exp STAR se2=static_exp { SBinOp(SMult, se1, se2) }
  | se1=static_exp SLASH se2=static_exp { SBinOp(SDiv, se1, se2) }
  /*bool ops*/
  | se1=static_exp EQUAL se2=static_exp { SBinOp(SEqual, se1, se2) }
  | se1=static_exp LEQ se2=static_exp { SBinOp(SLeq, se1, se2) }

exps: "(" e=slist(exp, ",") ")" {e}

exp: e=_exp { mk_exp ~loc:(Loc $sloc) e }
_exp:
  | e=_simple_exp  { e }
  | c=const { Econst c }
  | REG e=exp { Ereg e }
  | id=IDENTIFIER p=call_params a=exps { Ecall (id, p, a) }
  | e1=exp PLUS e2=exp { Ecall ("or", [], [e1; e2]) }
  | e1=exp OR e2=exp { Ecall ("or", [], [e1; e2]) }
  | e1=exp AND e2=exp { Ecall ("and", [], [e1; e2]) }
  | e1=exp CIRCUMFLEX e2=exp { Ecall("xor", [], [e1; e2]) }
  | e1=exp XOR e2=exp { Ecall ("xor", [], [e1; e2]) }
  | e1=exp NAND e2=exp { Ecall ("nand", [], [e1; e2]) }
  | NOT a=exp     { Ecall ("not", [], [a])}
  | e1=exp DOT e2=exp
    { Ecall("concat", [fresh_param(); fresh_param(); fresh_param ()], [e1; e2]) }
  | e1=simple_exp LBRACKET idx=static_exp RBRACKET
    { Ecall ("select", [idx; fresh_param()], [e1]) }
  | e1=simple_exp LBRACKET low=static_exp DOTDOT high=static_exp RBRACKET
    { Ecall("slice", [low; high; fresh_param()], [e1]) }
  | e1=simple_exp LBRACKET low=static_exp DOTDOT RBRACKET
    { let n = fresh_param () in
      let high = mk_static_exp (SBinOp(SMinus, n, mk_static_exp (SInt 1))) in
      Ecall("slice", [low; high; n], [e1]) }
  | e1=simple_exp LBRACKET DOTDOT high=static_exp RBRACKET
    {
      let params = [mk_static_exp (SInt 0); high; fresh_param ()] in
      Ecall("slice", params, [e1])
    }
  | ro=rom_or_ram "<" addr_size=static_exp
    COMMA word_size=static_exp input_file=tag_option(COMMA, STRING) ">" a=exps
    { Emem(ro, addr_size, word_size, input_file, a) }

simple_exp: e=_simple_exp { mk_exp ~loc:(Loc $sloc) e }
_simple_exp:
  | n=ident                   { Evar n }
  | "(" e=_exp ")"      { e }

const:
  | b=BOOL { VBit b }
  | i=INT
    { let (s, v) = i in VBitArray (bool_array_of_int s v) }
  | LBRACKET RBRACKET { VBitArray (Array.make 0 false) }

rom_or_ram :
  | ROM { MRom }
  | RAM { MRam }

call_params:
  | /*empty*/ { [] }
  | "<" pl=snlist(static_exp, ",") ">" { pl }

probe_decls:
  | /*empty*/ { [] }
  | PROBING l=snlist(ident, ",") { l }
%%

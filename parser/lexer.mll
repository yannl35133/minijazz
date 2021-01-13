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

{
open Location
open Lexing
open Parser
open Errors

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t)

let () = List.iter (fun (str, tok) -> Hashtbl.add keyword_table str tok) [
  "_", WILDCARD;
  "ram", RAM;
  "rom", ROM;
  "mux", MUX;
  "where", WHERE;
  "end", END;
  "true", BOOL true;
  "false", BOOL false;
  "reg", REG;
  "not", NOT;
  "const", CONST;
  "and", AND;
  "nand", NAND;
  "or", OR;
  "nor", NOR;
  "xor", XOR;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "inline", INLINE;
  "probing", PROBING;
  "type", TYPE;
  "match", MATCH;
  "with", WITH;
  "automaton", AUTOMATON;
  "local", LOCAL;
  "reset", RESET;
  "every", EVERY;
  (* "let", LET;
  "in", IN; *)
  "unless", UNLESS;
  "until", UNLESS;
  "continue", CONTINUE;
  "restart", RESTART;
  (* "do", DO;
  "done", DONE *)
]


let char_for_backslash = function
    'n' -> '\n'
  | 'r' -> '\r'
  | 'b' -> '\b'
  | 't' -> '\t'
  | c   -> c

let char_for_decimal_code code =
  let c = int_of_string code in
  char_of_int (c land 0xFF)

let size_of_base c =
  match c with
  | 'X' | 'x' -> 4
  | 'O' | 'o' -> 3
  | _ -> 1
}

let newline = '\n' | '\r' '\n'
let space = [' ' '\t']
let alphanum = ['A'-'Z' 'a'-'z' '_' '0'-'9']
let alpha = ['A'-'Z' 'a'-'z' '_']
let ascii = [' ' - '~'] # ['\\' '"']

let constructor = ['A'-'Z']alphanum*
let ident = alpha alphanum*

rule token = parse
  | newline         { new_line lexbuf; token lexbuf }
  | space+          { token lexbuf }
  | "|"             { BAR }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "*"             { STAR }
  | "+"             { PLUS }
  | "!"             { NOT }
  | "||"            { OR }
  | "&&"            { AND }
  | "&"             { AND }
  | "/"             { SLASH }
  | "<"             { LANGLE }
  | ">"             { RANGLE }
  | "["             { LBRACKET }
  | "]"             { RBRACKET }
  | ":"             { COLON }
  | ";"             { SEMICOL }
  | "="             { EQUAL }
  | "<>"            { NEQ }
  | ","             { COMMA }
  | "-"             { MINUS }
  | "^"             { CIRCUMFLEX }
  | "<="            { LEQ }
  | ">="            { GEQ }
  | "->"            { ARROW }
  | ".."            { DOTDOT }
  | "."             { DOT }
  | constructor as id {CONSTRUCTOR id }
  | ident as id     { try Hashtbl.find keyword_table id
                      with Not_found -> IDENT id }
  | '0' (['b' 'B'] as base)  (['0'-'1']+ as lit) as num
  |('0' (['u' 'U'] as base))?(['0'-'9']+ as lit) as num
  | '0' (['o' 'O'] as base)  (['0'-'7']+ as lit) as num
  | '0' (['x' 'X'] as base)  (['0'-'9' 'A'-'F' 'a'-'f']+ as lit) as num
                    { let b = match base with
                      | Some 'b' | Some 'B'        -> 1
                      | Some 'o' | Some 'O'        -> 3
                      | Some 'x' | Some 'X'        -> 4
                      | Some 'u' | Some 'U' | None -> -1 (* Will be re-interpreted as binary if netlist, with a warning *)
                      | _ -> invalid_arg "Not a valid base"
                      in
                      INT (String.length lit * b,
                           int_of_string num) }
  | "\""
      { string lexbuf.lex_start_p (Buffer.create 16) lexbuf }
  | "(*"
      { multi_comment lexbuf.lex_curr_p lexbuf; token lexbuf }
  | "#" " "* (['0'-'9']+ as line) " "*
    '"' (ascii* as file) '"'
     [' ' '0'-'9']* newline
        { let l = int_of_string line in
          lexbuf.lex_curr_p <-
            { lexbuf.lex_curr_p with
                pos_fname = file;
                pos_lnum  = l;
                pos_bol = lexbuf.lex_curr_p.pos_cnum
            };
          token lexbuf }
  | "#"
      { preprocess lexbuf }
  | "//"
      { single_comment lexbuf }
  | eof
      { EOF }
  | _
      { raise (Lexical_error (Illegal_character,
                      Loc (Lexing.lexeme_start_p lexbuf,
                      Lexing.lexeme_end_p lexbuf))) }

and multi_comment comment_start = parse
  | "(*"
      { multi_comment lexbuf.lex_curr_p lexbuf; multi_comment comment_start lexbuf }
  | "*)"
      { () }
  | eof
      { raise (Lexical_error (Unterminated_comment,
                    Loc(comment_start, Lexing.lexeme_start_p lexbuf))) }
  | "\""
      { ignore (string lexbuf.lex_curr_p (Buffer.create 16) lexbuf);
        multi_comment comment_start lexbuf }
  | newline
      { new_line lexbuf; multi_comment comment_start lexbuf}
  | _
      { multi_comment comment_start lexbuf }

and single_comment = parse
    newline
      { new_line lexbuf; token lexbuf }
  | eof
      { EOF }
  | _
      { single_comment lexbuf }

and string string_start buf = parse
    '"'
      { lexbuf.lex_start_p <- string_start;
        STRING (Buffer.contents buf) }
  | '\\' newline space* (* Backslash-escaped line return *)
      { new_line lexbuf; string string_start buf lexbuf }
  | '\\' (['\\' '"'  'n' 't' 'b' 'r'] as c)
      { Buffer.add_char buf (char_for_backslash c);
        string string_start buf lexbuf }
  | '\\' (['0'-'9'] ['0'-'9'] ['0'-'9'] as code)
      { Buffer.add_char buf (char_for_decimal_code code);
         string string_start buf lexbuf }
  | '\\'
      { raise (Lexical_error (Illegal_character,
                    Loc (string_start, Lexing.lexeme_start_p lexbuf))) }
  | '\n' | eof
      { raise (Lexical_error (Unterminated_string,
                    Loc (string_start, Lexing.lexeme_start_p lexbuf))) }
  | _ as c
      { Buffer.add_char buf c;
        string string_start buf lexbuf }

and preprocess = parse
    '\\' newline
      { new_line lexbuf; preprocess lexbuf }
  | newline
      { new_line lexbuf; token lexbuf }
  | eof
      { EOF }
  | _
      { preprocess lexbuf }

(* eof *)

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

exception Lexical_error of lexical_error * location;;

let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
 "ram", RAM;
 "rom", ROM;
 "where", WHERE;
 "end", END;
 "true", BOOL(true);
 "false", BOOL(false);
 "reg", REG;
 "not", NOT;
 "const", CONST;
 "and", AND;
 "nand", NAND;
 "or", OR;
 "xor", XOR;
 "if", IF;
 "then", THEN;
 "else", ELSE;
 "inlined", INLINED;
 "probing", PROBING
]


(* To buffer string literals *)

let initial_string_buffer = Bytes.create 256
let string_buff = ref initial_string_buffer
let string_index = ref 0

let reset_string_buffer () =
  string_buff := initial_string_buffer;
  string_index := 0;
  ()

let store_string_char c =
  if !string_index >= Bytes.length (!string_buff) then begin
    let new_buff = Bytes.create (Bytes.length (!string_buff) * 2) in
      Bytes.blit (!string_buff) 0 new_buff 0 (Bytes.length (!string_buff));
      string_buff := new_buff
  end;
  Bytes.set (!string_buff) (!string_index) c;
  incr string_index


let get_stored_string () =
  let s = Bytes.sub_string (!string_buff) 0 (!string_index) in
  string_buff := initial_string_buffer;
  s

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
let alpha = ['A'-'Z' 'a'-'z']
let ascii = [' ' - '~'] # ['\\' '"']

let ident = alpha alphanum*

rule token = parse
  | newline         { new_line lexbuf; token lexbuf }
  | space+          { token lexbuf }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "*"             { STAR }
  | "+"             { PLUS }
  | "&"             { AND }
  | "/"             { SLASH }
  | "<"             { LESS }
  | ">"             { GREATER }
  | "["             { LBRACKET }
  | "]"             { RBRACKET }
  | ":"             { COLON }
  | ";"             { SEMICOL }
  | "="             { EQUAL }
  | ","             { COMMA }
  | "-"             { MINUS }
  | "^"             { POWER }
  | "<="            { LEQ }
  | "."             { DOT }
  | ".."            { DOTDOT }
  | ident as id
                    { try Hashtbl.find keyword_table id
                      with Not_found -> NAME id }
  | '0' (['b' 'B'] as base)  (['0'-'1']+ as lit) as num
  |('0' (['u' 'U'] as base)?)(['0'-'9']+ as lit) as num
  | '0' (['o' 'O'] as base)  (['0'-'7']+ as lit) as num
  | '0' (['x' 'X'] as base)  (['0'-'9' 'A'-'F' 'a'-'f']+ as lit) as num
                    { let b = match base with
                      | Some 'b' | Some 'B'        -> 1
                      | Some 'o' | Some 'O'        -> 3
                      | Some 'x' | Some 'X'        -> 4
                      | Some 'u' | Some 'U' | None -> 4
                      | _ -> invalid_arg "Not a valid base"
                      in
                      INT (String.length lit * b,
                            int_of_string num) }
  | "\""
      { reset_string_buffer ();
        string lexbuf.lex_start_p lexbuf }
  | "(*"
      { comment lexbuf.lex_curr_p lexbuf; token lexbuf }
  | "#" " "* (['0'-'9']+ as line) " "*
    '"' (ascii* as file) '"' 
     [' ' '0'-'9']* newline
        {
            let l = int_of_string line in
            lexbuf.lex_curr_p <- {
                lexbuf.lex_curr_p with
                pos_fname = file;
                pos_lnum  = l;
                pos_bol = lexbuf.lex_curr_p.pos_cnum
            };
            token lexbuf
        }
  | "#"
      { preprocess lexbuf;
        token lexbuf }
  | eof            {EOF}
  | _              {raise (Lexical_error (Illegal_character,
                      Loc (Lexing.lexeme_start_p lexbuf,
                      Lexing.lexeme_end_p lexbuf)))}

and comment comment_start = parse
  | "(*"
      { comment lexbuf.lex_curr_p lexbuf; comment comment_start lexbuf }
  | "*)"
      { () }
  | eof
      { raise (Lexical_error (Unterminated_comment,
                    Loc(comment_start, Lexing.lexeme_start_p lexbuf))) }
  | "\""
      { reset_string_buffer ();
        ignore (string lexbuf.lex_curr_p lexbuf);
        comment comment_start lexbuf }
  | newline
      {new_line lexbuf; comment comment_start lexbuf}
  | _
      { comment comment_start lexbuf }

and string string_start = parse
    '"'
      { lexbuf.lex_start_p <- string_start;
        STRING (get_stored_string ()) }
  | '\\' newline space* (* Backslash-escaped line return *)
      { new_line lexbuf; string string_start lexbuf }
  | '\\' (['\\' '"'  'n' 't' 'b' 'r'] as c)
      { store_string_char (char_for_backslash c);
        string string_start lexbuf }
  | '\\' (['0'-'9'] ['0'-'9'] ['0'-'9'] as code)
      { store_string_char (char_for_decimal_code code);
         string string_start lexbuf }
  | eof
      { raise (Lexical_error (Unterminated_string,
                    Loc (string_start, Lexing.lexeme_start_p lexbuf))) }
  | _ as c
      { store_string_char c;
        string string_start lexbuf }

and preprocess = parse
  | newline
      { new_line lexbuf }
  | _
      { preprocess lexbuf }

(* eof *)


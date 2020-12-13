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

open Errors
open Cli_options
open Location
open Format

let parse lexbuf =
  try Parser.program Lexer.token lexbuf
  with
  | Lexical_error (err, l) ->
     lexical_error err l
  | Parser.Error ->
     let pos1 = Lexing.lexeme_start_p lexbuf
     and pos2 = Lexing.lexeme_end_p lexbuf in
     let l = Loc (pos1,pos2) in
     syntax_error l

let lexbuf_from_file file_name =
  let ic = open_in file_name in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.Lexing.lex_curr_p <-
    { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = file_name };
  ic, lexbuf

let compile_impl filename =
  (* input and output files *)
  if not (Filename.check_suffix filename "mj")
  then (eprintf "Invalid filename %s: must end with .mj@." filename; exit 1);

  let ic, lexbuf = lexbuf_from_file filename in
  let net_name = (Filename.chop_suffix filename ".mj") ^ ".net" in
  let net = open_out net_name in
  let quit code =
    close_in ic;
    close_out net;
    exit code
  in
  try
    base_path := Filename.dirname filename;

    let parsing_ast = parse lexbuf in

    if !print_parsing_ast then
      Printers.ParserAst.print_program parsing_ast Format.std_formatter;

    if !parse_only then quit 0;

    let static_scoped_ast = Static_scoping.program parsing_ast in
    (* let static_typed_ast = Static_typer.program static_scoped_ast in
     * let _netlist_dim_ast = Netlist_dimensioning.program static_typed_ast in *)

    if !type_only then quit 0;

    quit 0
  with
  | ErrorDetected -> quit 1;
  | x -> raise x

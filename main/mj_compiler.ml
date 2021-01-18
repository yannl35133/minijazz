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
open Printers

type stop_exec =
  | Parsing
  | StaticParsing
  | Typing
  | Compiling

let separateur = "\n*********************************************\
    *********************************\n*** "

let comment ?(sep=separateur) s =
  if !verbose then Format.printf "%s%s@." sep s

let do_pass pass_name f program printer =
  comment (pass_name ^ " ...\n");
  let r = f program in
  if !verbose then
    Format.printf "%t" (printer r);
  comment ~sep:"*** " (pass_name ^ " done.");
  r

let do_silent_pass pass_name f program = do_pass pass_name f program (fun _ -> CommonAst.dprint_nop)

let pass pass_name enabled f program printer =
  if enabled
  then do_pass pass_name f program printer
  else program

let silent_pass pass_name enabled f program =
  if enabled
  then do_silent_pass pass_name f program
  else program

let parse lexbuf =
  try
    Parser.program Lexer.token lexbuf
  with
    | Lexical_error (err, l) ->
        lexical_error err l
    | Parser_error_deep loc ->
        syntax_error loc
    | Parser.Error ->
        let pos1 = Lexing.lexeme_start_p lexbuf
        and pos2 = Lexing.lexeme_end_p lexbuf in
        let l = Loc (pos1, pos2) in
        syntax_error l

let lexbuf_from_file file_name =
  let ic = open_in file_name in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf file_name;
  ic, lexbuf

let dbg_printer p =
  ParserAst.print_program (Sizer_to_parser.program p)
  (* NetlistSizedAst.print_program p *)

let compile_impl filename =
  (* input and output files *)
  if not (Filename.check_suffix filename "mj") then begin
    Format.eprintf "Invalid filename %s: must end with .mj@." filename;
    exit 1
  end;

  let ic, lexbuf = lexbuf_from_file filename in
  let net_name = (Filename.chop_suffix filename ".mj") ^ ".net" in

  try
    let _printer_sized prog = Printers.NetlistSizedAst.print_program prog Format.std_formatter in
    let printer_original = (fun p fmt -> Printer.print_program fmt p) in

    let p = do_pass "Parsing"                        parse lexbuf ParserAst.print_program in

    if !print_parsing_ast then
      Printers.ParserAst.print_program p Format.std_formatter;

    let p = do_pass "Scoping"                Static_scoping.program p (fun _ _ -> ()) (* StaticScopedAst.print_program *) in
    let p = do_pass "Typing static"            Static_typer.program p StaticTypedAst.print_program in
    let p = do_pass "Dimensioning"     Netlist_dimensioning.program p NetlistDimensionedAst.print_program in
    let p = do_pass "Constraining"        Netlist_constrain.program p (fun _ _ -> ()) (* NetlistConstrainedAst.print_program *) in
    let p = do_pass "Sizing"                  Netlist_sizer.program p NetlistSizedAst.print_program in

    let p = pass "dedimension"  true            Dedimension.program p dbg_printer in
    let p = pass "rename_local" false          Rename_local.program p dbg_printer in
    let p = pass "deautomaton"  true              Automaton.program p dbg_printer in
    let p = pass "dereset"      true                  Reset.program p dbg_printer in
    let p = pass "dematch"      true                Matcher.program p dbg_printer in

    let p = do_pass "Translate to MJ original" Sized_to_old.program p printer_original in

    let p = pass "Scoping"      true                Scoping.program p printer_original in
    let p = pass "Typing"       true                 Typing.program p printer_original in
    let p = pass "Normalize"    true              Normalize.program p printer_original in
    let p = pass "Callgraph"    true              Callgraph.program p printer_original in
    let p = pass "Simplify"     true               Simplify.program p printer_original in

    let p = Mj2net.program p in

    let p = silent_pass "Simplify netlist" !netlist_simplify Netlist_simplify.simplify p in

    if not !no_netlist then begin
      let net = open_out net_name in
      let p = Netlist_simplify.simplify p in
      Netlist_printer.print_program net p;
      close_out net
    end
  with
  | x -> close_in ic; raise x

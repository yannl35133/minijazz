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

open Cli_options
open Mj_compiler

let main () =
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-m", Arg.Set_string main_node, doc_main_node;
        "-S", Arg.Set netlist_simplify, doc_netlist_simplify;
        "-print-types", Arg.Set print_types, doc_full_type_info;
        "-print-parsing-ast", Arg.Set print_parsing_ast, doc_parsing_ast;
        "-parse-only", Arg.Set parse_only, doc_parse_only;
        "-type-only", Arg.Set type_only, doc_type_only;
      ]
      compile_impl
      errmsg
  with
    | Errors.ErrorDetected -> exit 2;;

let () = main ()

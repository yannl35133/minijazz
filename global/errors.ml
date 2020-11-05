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

open Location

exception ErrorDetected

type lexical_error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string
  | Nonbinary_base

exception Lexical_error of lexical_error * location

let lexical_error err loc =
  Format.eprintf "%aSyntax error: %s"
    print_location loc
    (match err with
    | Illegal_character     -> "illegal character@."
    | Unterminated_comment  -> "unterminated comment@."
    | Unterminated_string   -> "unterminated string@."
    | Nonbinary_base -> "base unadapted to binary@."
    );
  raise ErrorDetected

let syntax_error loc =
  Format.eprintf "%aSyntax error@." print_location loc;
  raise ErrorDetected

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

exception TmpError

type lexical_error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string

type lexical_warning =
  | Nonbinary_base of Location.location

exception Lexical_error of lexical_error * Location.location

(** name of undefined constant *)
exception Scope_error of string * Location.location

(** name of not-a-type *)
exception NotAType of string * Location.location

(** Observed type, expected type, expression location *)
exception WrongType of (string * string * Location.location)

exception NoTypes of Location.location
exception TwoTypes of Location.location

(** Function expected types (as a hint), observed type, expected type, expression location *)
exception WrongTypeParam of (string list * string * string * Location.location)


open Location

exception ErrorDetected

let lexical_error err loc =
  Format.eprintf "%aSyntax error: %s"
  print_location loc
  (match err with
  | Illegal_character     -> "illegal character@."
  | Unterminated_comment  -> "unterminated comment@."
  | Unterminated_string   -> "unterminated string@."
  );
  raise ErrorDetected
  
let syntax_error loc =
  Format.eprintf "%aSyntax error@." print_location loc;
  raise ErrorDetected

let raise_warning = function
  | Nonbinary_base loc-> ignore "base unadapted to binary@."; ()
    
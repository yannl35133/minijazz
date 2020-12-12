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

(** Observed type, expected type, expression location, function name, function expected types (as a hint) *)
exception WrongTypeParam of (string * string * Location.location * string * string list)

(** Constant value contains a 0-wide bus as a dimension *)
exception ZeroWideBusMulti of (int * Location.location)

(** Constant value does not have a unique dimension *)
exception NonConstantDimension of Location.location

(** Obtained a product type where it is unexpected: where it is unexpected, expression location *)
exception UnexpectedProd of (string * Location.location)

(** Observed dimension, expected dimension, expression location *)
exception WrongDimension of (int * int * Location.location)

(** Observed dimension, expected dimension, expression location, function name, function expected dimensions *)
exception WrongDimensionArg of (int * int * Location.location * string * string list)  (* TO BE REDONE *)

(** Observed dimension, expected dimension, expression location, operator name, dimensioned reference location *)
exception WrongDimensionOp of (int * int * Location.location * string * Location.location)

(** Observed number of arguments, function call location, expected number of arguments, name of function *)
exception WrongNumberArguments of (int * Location.location * int * string)

(** Dimension of argument, number of times sliced, location *)
exception SliceTooMuch of (int * int * Location.location)

type dimension_warning =
  | InsufficientAnnotations of (string * Location.location * string) (** function name, case location, variable undimensionable *)

(** Constant value does not have a unique dimension *)
exception NonConstantSize of Location.location

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

let raise_warning_lexical = function
  | Nonbinary_base _loc -> ignore "base unadapted to binary@."

let raise_warning_dimension = function
  | InsufficientAnnotations (_name, _loc, _var) -> ()

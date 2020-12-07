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

let fold_lefti f acc li =
  snd @@ List.fold_left (fun (i, acc) el -> (i + 1, f acc i el)) (0, acc) li

let fold_left_map2 f acc l1 l2 =
  let rec fold_left_map2_f (acc, res_l) l1 l2 = match l1, l2 with
    | [], [] -> acc, List.rev res_l
    | hd1 :: tl1, hd2 :: tl2 ->
        let acc', r = f acc hd1 hd2 in fold_left_map2_f (acc', r :: res_l) tl1 tl2
    | _::_, [] | [], _::_ -> invalid_arg "fold_left_map2"
  in
  fold_left_map2_f (acc, []) l1 l2

let option_get ?(error=Invalid_argument "option_get") opt =
  match opt with
    | None -> raise error
    | Some thing -> thing


(* Functions to decompose a list into a tuple *)
exception Arity_error of int * int (*expected, found*)
exception Arity_min_error of int * int (*expected, found*)

let try_1 = function
  | [v] -> v
  | l -> raise (Arity_error(1, List.length l))

let try_2 = function
  | [v1; v2] -> v1, v2
  | l -> raise (Arity_error(2, List.length l))

let try_3 = function
  | [v1; v2; v3] -> v1, v2, v3
  | l -> raise (Arity_error(3, List.length l))

let try_4 = function
  | [v1; v2; v3; v4] -> v1, v2, v3, v4
  | l -> raise (Arity_error(4, List.length l))

let try_1min = function
  | v::l -> v, l
  | l -> raise (Arity_min_error(1, List.length l))

let assert_fun f l =
  try
    f l
  with
      Arity_error(expected, found) ->
        Format.eprintf "Internal compiler error: \
     wrong list size (found %d, expected %d).@." found expected;
        assert false

let assert_min_fun f l =
  try
    f l
  with
      Arity_min_error(expected, found) ->
        Format.eprintf "Internal compiler error: \
     wrong list size (found %d, expected %d at least).@." found expected;
        assert false

let assert_1 l = assert_fun try_1 l
let assert_2 l = assert_fun try_2 l
let assert_3 l = assert_fun try_3 l
let assert_4 l = assert_fun try_4 l

let assert_1min l = assert_min_fun try_1min l

let mapfold f acc l =
  let l,acc = List.fold_left
                (fun (l,acc) e -> let e,acc = f acc e in e::l, acc)
                ([],acc) l in
  List.rev l, acc

let mapi f l =
  let rec aux i = function
    | [] -> []
    | v::l -> (f i v)::(aux (i+1) l)
  in
    aux 1 l

let unique l =
  let tbl = Hashtbl.create (List.length l) in
  List.iter (fun i -> Hashtbl.replace tbl i ()) l;
  Hashtbl.fold (fun key _ accu -> key :: accu) tbl []

let is_empty = function | [] -> true | _ -> false

let gen_symbol =
  let counter = ref 0 in
  let _gen_symbol () =
    counter := !counter + 1;
    "_"^(string_of_int !counter)
  in
    _gen_symbol

let bool_of_string s = match s with
  | "t" | "1" -> true
  | "f" | "0" -> false
  | _ -> raise (Invalid_argument ("bool_of_string"))

let bool_array_of_string s =
  let a = Array.make (String.length s) false in
  for i = 0 to String.length s - 1 do
    a.(i) <- bool_of_string (String.sub s i 1)
  done;
  a

let bool_list_of_int (nbits, v) =
  List.init nbits (fun n -> v land (1 lsl (nbits - 1 - n)) <> 0)

let exp a n =
  let rec aux acc n =
    if n = 0 then 1
    else if n = 1 then acc
    else if n land 1 <> 0 then aux (acc * a) (n lsl 1)
    else aux acc (n lsl 1)
  in aux 1 n

let bool_list_of_dec_int (nbits, v) =
  List.init (-nbits) (fun n -> v / (exp 10 n) mod (exp 10 (n + 1)) = 1)

exception Int_too_big
let convert_size s n =
  let m = String.length s in
  if m > n then
    raise Int_too_big
  else
    if m = n then s else (String.make (n - m) '0')^s

let binary_not s =
  String.map (fun c -> if c = '0' then '1' else '0') s

let rec binary_string_of_int i n =
  let rec s_of_i i = match i with
    | 0 -> "0"
    | 1 -> "1"
    | i when i < 0 -> binary_not (binary_string_of_int (-i-1) n)
    | _ ->
      let q, r = i / 2, i mod 2 in
      (s_of_i q) ^ (s_of_i r)
  in
  convert_size (s_of_i i) n

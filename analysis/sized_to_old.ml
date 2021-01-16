open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST
open Static
open Ast_old

let unused = let n = ref 0 in fun () -> incr n; "unused_variable_number" ^ string_of_int !n

let ident id = Ident.ident_of_string (!*!id ^ UIDIdent.to_string !**id)

(* | SAdd | SMinus | SMult | SDiv | SPower (*int*)
| SEqual | SLess | SLeq | SGreater | SGeq (* bool *) *)

let binop : int_op -> sop = function
  | SAdd -> SAdd    | SMinus -> SMinus
  | SMult -> SMult  | SDiv -> SDiv
  | SPower -> SPower

let bool_binop : int_bool_op -> sop = function
  | SEq -> SEqual | SNeq -> SNeq
  | SLt -> SLess | SLeq -> SLeq
  | SGt -> SGreater | SGeq -> SGeq

let rec static_int_exp_desc : static_int_exp_desc -> static_exp_desc = function
  | SInt n -> SInt n
  | SIParam id -> SVar !*!id
  | SIConst id -> SVar !*!id
  | SIUnOp (SNeg, se) -> SBinOp (SMinus, mk_static_int 0, static_int_exp se)
  | SIBinOp (op, se1, se2) -> SBinOp (binop op, static_int_exp se1, static_int_exp se2)
  | SIIf (c, se1, se2) -> SIf (static_bool_exp c, static_int_exp se1, static_int_exp se2)

and static_int_exp e = mk_static_exp ~loc:!@e (static_int_exp_desc !!e)

and static_bool_exp_desc : static_bool_exp_desc -> static_exp_desc = function
  | SBool b -> SBool b
  | SBParam _ -> assert false
  | SBConst _ -> assert false
  | SBUnOp (SNot, _) -> assert false
  | SBBinOp _ -> assert false
  | SBBinIntOp (op, se1, se2) -> SBinOp (bool_binop op, static_int_exp se1, static_int_exp se2)
  | SBIf (c, se1, se2) -> SIf (static_bool_exp c, static_bool_exp se1, static_bool_exp se2)

and static_bool_exp e = mk_static_exp ~loc:!@e (static_bool_exp_desc !!e)

let static_bitype_exp e = match !!e with
  | SIntExp  e' -> mk_static_exp ~loc:!@e (static_int_exp_desc  e')
  | SBoolExp e' -> mk_static_exp ~loc:!@e (static_bool_exp_desc e')


let params p = List.map (fun p -> mk_param !*!(p.sti_name)) p

let mem_kind : mem_kind_desc -> mem_kind = function
  | MRam -> MRam
  | MRom -> MRom

let rec value = function
  | VNDim l -> VBitArray (Array.of_list (List.map (function VBit b -> b | _ -> assert false) @@ List.map value l))
  | VBit b -> VBit b


let rec exp e =
  let regex = Str.regexp {|\(or\|and\|xor\|nand\|nor\|not\|mux\)_\([01]\)|} in
  mk_exp ~loc:!$@e @@ match !$!e with
  | EConst v -> Econst (value v)
  | EVar id ->  Evar (ident id)
  | EReg e ->   Ereg (exp e)
  | ECall (funname, [p1; p2], args) when !!funname = "slice_one" -> Ecall ("select", List.map static_bitype_exp [p2; p1], List.map exp args)
  | ECall (funname, [p], args) when !!funname = "slice_all" ->
      let size = static_bitype_exp p in
      Ecall ("slice", [mk_static_int 0; mk_static_exp (SBinOp (SMinus, size, mk_static_int 1)); size], List.map exp args)
  | ECall (funname, [p1; p2], args) when !!funname = "slice_from" ->
      let size = static_bitype_exp p1 in
      Ecall ("slice", [static_bitype_exp p2; mk_static_exp (SBinOp (SMinus, size, mk_static_int 1)); size], List.map exp args)
  | ECall (funname, [p1; p2], args) when !!funname = "slice_to" ->
      Ecall ("slice", [mk_static_int 0; static_bitype_exp p2; static_bitype_exp p1], List.map exp args)
  | ECall (funname, [p1; p2; p3], args) when !!funname = "slice_fromto" ->
      Ecall ("slice", [static_bitype_exp p2; static_bitype_exp p3; static_bitype_exp p1], List.map exp args)
  | ECall (funname, p, args) when Str.string_match regex !!funname 0 ->
      let op = Str.matched_group 1 !!funname in
      let dim = int_of_string @@ Str.matched_group 2 !!funname in
      if dim = 1 then
        Ecall ("n_" ^ op, List.map static_bitype_exp p, List.map exp args)
      else
        Ecall (op, List.map static_bitype_exp p, List.map exp args)
  | ECall (funname, [], [e]) when !!funname = "add_dim_0" -> (exp e).e_desc
  | ECall (funname, [p1; p2], args) when !!funname = "concat_1" ->
      let p1, p2 = static_bitype_exp p1, static_bitype_exp p2 in
      let p_out = mk_static_exp (SBinOp (SAdd, p1, p2)) in
      Ecall ("concat", [p1; p2; p_out], List.map exp args)
  | ECall (funname, p, args) -> Ecall (!!funname, List.map static_bitype_exp p, List.map exp args)
      (* function * params * args *)
  | EMem (m, (addr_size, word_size, file), args) -> Emem (mem_kind !!m, static_int_exp addr_size, static_int_exp word_size, file, List.map exp args)
      (* ro * (address size * word size * input file) * args *)


let tritype_exp = function
  | Exp e -> exp e
  | _ -> assert false

let type_ident t = match !!t with
  | BNetlist TNDim [] -> TBit
  | BNetlist TNDim [Size s] -> TBitArray (mk_static_exp ~loc:!@t (static_int_exp_desc s))
  | _ -> assert false


let rec lvalue lval = match !?!lval with
  | LValDrop -> Evarpat (Ident.ident_of_string (unused ()))
  | LValId id -> Evarpat (ident id)
  | LValTuple l -> Etuplepat (List.map (function Evarpat id -> id | _ -> assert false) @@ List.map lvalue l)

let decl d = match d with
  | Deq (lval, e)
  | Dlocaleq (lval, e) -> (lvalue lval, tritype_exp e)
  | _ -> assert false

let block b = BEqs (List.map decl b, [])

let rec body b = match List.map (!!) b with
  | [Dif (c, b1, b2)] -> BIf (static_bool_exp c, body b1, body b2)
  | b -> block b

let const ({ const_name; const_decl; const_loc } : NetlistSizedAST.const) : const_dec =
  { c_name = !*!const_name; c_value = static_bitype_exp const_decl; c_loc = const_loc }

let inline : inline_status -> inlined_status = function
  | Inline -> Inlined
  | NotInline -> NotInlined

let starput = List.map (fun ti -> mk_var_dec (ident (ti.ti_name)) (type_ident ti.ti_type))

let node { node_name; node_loc; node_params; node_inline; node_inputs; node_outputs; node_body; _ } : node_dec =
  { n_name = !!node_name; n_loc = node_loc; n_inlined = inline node_inline;
  n_inputs = starput node_inputs; n_outputs = starput node_outputs;
  n_params = params node_params; n_constraints = [];
  n_body = body node_body; n_probes = [] }

let program ({ p_enums; p_consts; p_consts_order; p_nodes }: NetlistSizedAST.program) : program =
  assert (p_enums = ConstructEnv.empty);
  let p_nodes = List.map snd @@ List.of_seq @@ FunEnv.to_seq @@ FunEnv.map node p_nodes in
  let p_consts = List.map (fun uid -> const @@ Env.find uid p_consts) p_consts_order in
  { p_nodes; p_consts }

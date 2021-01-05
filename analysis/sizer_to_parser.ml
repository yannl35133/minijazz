(** Convert netlist sized ast to parser ast
    usefull for debugging puposes *)

open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* convert static operators *)

let cvt_int_op : int_op -> ParserAST.sop = function
  | SAdd -> SAdd
  | SMinus -> SMinus
  | SMult -> SMult
  | SDiv -> SDiv
  | SPower -> SPower

let cvt_int_bool_op : int_bool_op -> ParserAST.sop = function
  | SEq -> SEq
  | SNeq -> SNeq
  | SLt -> SLt
  | SLeq -> SLeq
  | SGt -> SGt
  | SGeq -> SGeq

let cvt_bool_op : bool_op -> ParserAST.sop = function
  | SOr -> SOr
  | SAnd -> SAnd

let cvt_int_unop : int_unop -> ParserAST.sunop = function
  | SNeg -> SNeg

let cvt_bool_unop : bool_unop -> ParserAST.sunop = function
  | SNot -> SNot

(* convert static expressions *)

let rec cvt_static_bool_exp_desc e: ParserAST.static_exp_desc =
  match e with
  | SBool b -> SBool b
  | SBParam _ -> assert false
  | SBConst id -> SIdent id
  | SBUnOp (op, se) -> SUnOp (cvt_bool_unop op, cvt_static_bool_exp se)
  | SBBinOp (op, s1, s2) ->
     let s1 = cvt_static_bool_exp s1 in
     let s2 = cvt_static_bool_exp s2 in
     SBinOp (cvt_bool_op op, s1, s2)
  | SBBinIntOp (op, s1, s2) ->
     let s1 = cvt_static_int_exp s1 in
     let s2 = cvt_static_int_exp s2 in
     SBinOp (cvt_int_bool_op op, s1, s2)
  | SBIf (c, s1, s2) ->
     let s1 = cvt_static_bool_exp s1 in
     let s2 = cvt_static_bool_exp s2 in
     SIf (cvt_static_bool_exp c, s1, s2)

and cvt_static_bool_exp e: ParserAST.static_exp =
  relocalize e.loc @@ cvt_static_bool_exp_desc e.desc

and cvt_static_int_exp_desc e: ParserAST.static_exp_desc =
  match e with
  | SInt i -> SInt i
  | SIParam i -> SInt i
  | SIConst v -> SIdent v
  | SIUnOp (op, e) -> SUnOp (cvt_int_unop op, cvt_static_int_exp e)
  | SIBinOp (op, s1, s2) ->
     let s1 = cvt_static_int_exp s1 in
     let s2 = cvt_static_int_exp s2 in
     SBinOp (cvt_int_op op, s1, s2)
  | SIIf (c, s1, s2) ->
     let s1 = cvt_static_int_exp s1 in
     let s2 = cvt_static_int_exp s2 in
     SIf (cvt_static_bool_exp c, s1, s2)

and cvt_static_int_exp e: ParserAST.static_exp =
  relocalize e.loc @@ cvt_static_int_exp_desc e.desc

let cvt_opt_static_int_exp e: ParserAST.optional_static_exp =
  relocalize e.loc @@ ParserAST.SExp (cvt_static_int_exp_desc e.desc)

let cvt_static_bitype_exp_desc e: ParserAST.static_exp_desc =
  match e with
  | SIntExp ie -> cvt_static_int_exp_desc ie
  | SBoolExp be -> cvt_static_bool_exp_desc be

let cvt_static_bitype_exp e: ParserAST.static_exp =
  relocalize !@e @@ cvt_static_bitype_exp_desc e.desc

let cvt_opt_static_bitype_exp e: ParserAST.optional_static_exp =
  relocalize e.loc @@ ParserAST.SExp (cvt_static_bitype_exp_desc e.desc)

(* convert types *)

let unfold_size = function Size se -> se

let rec cvt_netlist_size sz : ParserAST.netlist_type = match sz with
  | TProd nsz -> TProd (List.map cvt_netlist_size nsz)
  | TDim lst ->
     let aux x =
       let opt = ParserAST.SExp (cvt_static_int_exp_desc (unfold_size x)) in
       no_localize opt in
     TNDim (List.map aux lst)

let cvt_static_typed_ident t : ParserAST.static_typed_ident =
  let desc = t.desc in
  let ty = static_type_to_string desc.st_type.desc in
  relocalize t.loc
    ParserAST.{ st_name = desc.st_name;
                st_type_name = relocalize desc.st_type.loc ty }

let cvt_typed_ident (t:typed_ident) : ParserAST.typed_ident =
  let desc = t.desc in
  let netlist_typed = cvt_netlist_size desc.size.desc in
  relocalize t.loc
    ParserAST.{ name = desc.name;
                typed = relocalize desc.size.loc netlist_typed }

(* remove size from lvalue *)

let rec cvt_lvalue_desc (lv:lvalue_desc) : ParserAST.lvalue_desc =
  match lv with
  | LValDrop -> LValDrop
  | LValId id -> LValId id
  | LValTuple lvs -> LValTuple (List.map cvt_lvalue lvs)

and cvt_lvalue (lv:lvalue) : ParserAST.lvalue =
  relocalize lv.s_loc @@ cvt_lvalue_desc lv.s_desc

(* convert automaton/match handler *)

let rec cvt_match_hdl hdl : (ParserAST.exp, ParserAST.decl) match_hdl =
  { m_constr = hdl.m_constr; m_body = cvt_decl hdl.m_body}

and cvt_escape esc : (ParserAST.exp, ParserAST.decl) escape =
  { e_cond     = cvt_exp esc.e_cond;
    e_reset    = esc.e_reset;
    e_body     = cvt_decl esc.e_body;
    e_nx_state = esc.e_nx_state }

and cvt_automaton_hdl hdl : (ParserAST.exp, ParserAST.decl) automaton_hdl =
  { s_state  = hdl.s_state;
    s_vars   = hdl.s_vars;
    s_body   = cvt_decl hdl.s_body;
    s_until  = List.map cvt_escape hdl.s_until;
    s_unless = List.map cvt_escape hdl.s_unless }

(* convert expressions and declarations *)

and cvt_exp_desc (e:exp_desc) : ParserAST.exp_desc =
  match e with
  | EConst v -> EConst v
  | EConstr c -> EConstr c
  | EVar id -> EVar id
  | EReg e -> EReg (cvt_exp e)
  | ECall (fname, ps, args) ->
     ECall (fname,
            List.map cvt_opt_static_bitype_exp ps,
            List.map cvt_exp args)
  | EMem (kd, (a, w, f), args) ->
     EMem (kd, (cvt_opt_static_int_exp a, cvt_opt_static_int_exp w, f),
           List.map cvt_exp args)

and cvt_exp (e:exp) = relocalize e.s_loc @@ cvt_exp_desc e.s_desc

and cvt_decl_desc (d:decl_desc) : ParserAST.decl_desc =
  match d with
  | Dempty -> Dempty
  | Deq (lv, e) -> Deq (cvt_lvalue lv, cvt_exp e)
  | Dblock ds -> Dblock (List.map cvt_decl ds)
  | Dreset (d, e) -> Dreset (cvt_decl d, cvt_exp e)
  | Dautomaton hdls -> Dautomaton (List.map cvt_automaton_hdl hdls)
  | Dmatch (e, hdls) -> Dmatch (cvt_exp e, List.map cvt_match_hdl hdls)
  | Dif (c, c1, c2) ->
     Dif (cvt_static_bool_exp c, cvt_decl c1.block, cvt_decl c2.block)

and cvt_decl (d:decl) = relocalize !@d @@ cvt_decl_desc !!d

(* convert nodes *)

let cvt_node name desc lst: ParserAST.node list =
  let n: ParserAST.node_desc =
    { node_name    = relocalize desc.node_name_loc name;
      node_inline  = desc.node_inline;
      node_inputs  = List.map cvt_typed_ident desc.node_inputs;
      node_outputs = List.map cvt_typed_ident desc.node_outputs;
      node_params  = List.map cvt_static_typed_ident desc.node_params;
      node_body    = cvt_decl desc.node_body;
      node_probes  = desc.node_probes } in
  relocalize desc.node_loc n :: lst

let cvt_const id desc lst: ParserAST.const list =
  let c: ParserAST.const_desc =
    { const_left  = relocalize desc.const_ident id;
      const_right = cvt_static_bitype_exp desc.const_decl } in
  relocalize desc.const_total c :: lst

let program p: ParserAST.program =
  { p_enums = p.p_enums;
    p_consts = Env.fold cvt_const p.p_consts [];
    p_nodes = Env.fold cvt_node p.p_nodes [] }

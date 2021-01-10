(** Convert netlist sized ast to parser ast
    usefull for debugging puposes *)

open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let cvt_ident id = relocalize !*@id !*!id

let cvt_enum { enum_name; _ } =
  cvt_ident enum_name

let cvt_enum_full { enum_name; enum_constructors_names; enum_constructors = _; enum_loc } =
  ParserAST.{ enum_name = cvt_ident enum_name; enum_loc;
    enum_constructors = List.map cvt_ident enum_constructors_names }


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
  | SBParam id -> SIdent (relocalize !*@id !*!id)
  | SBConst id -> SIdent (relocalize !*@id !*!id)
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
  | SIParam id -> SIdent (relocalize !*@id !*!id)
  | SIConst id -> SIdent (relocalize !*@id !*!id)
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
  relocalize e.loc @@ SExp (cvt_static_int_exp_desc e.desc)

let cvt_static_bitype_exp_desc e: ParserAST.static_exp_desc =
  match e with
  | SIntExp ie -> cvt_static_int_exp_desc ie
  | SBoolExp be -> cvt_static_bool_exp_desc be

let cvt_static_bitype_exp e: ParserAST.static_exp =
  relocalize !@e @@ cvt_static_bitype_exp_desc e.desc

let cvt_opt_static_bitype_exp e: ParserAST.optional_static_exp =
  relocalize e.loc @@ SExp (cvt_static_bitype_exp_desc e.desc)

(* convert types *)

let unfold_size = function Size se -> se

let rec cvt_netlist_size sz : ParserAST.netlist_type = match sz with
  | TProd nsz -> TProd (List.map cvt_netlist_size nsz)
  | TNDim lst ->
     let aux x =
       let opt = SExp (cvt_static_int_exp_desc (unfold_size x)) in
       no_localize opt in
     TNDim (List.map aux lst)

let cvt_global_type : 'a -> ParserAST.global_type = function
  | BNetlist t -> BNetlist (cvt_netlist_size t)
  | BState enum -> BState (cvt_enum enum)
  | BStateTransition enum -> BStateTransition (cvt_enum enum)

let cvt_static_typed_ident { sti_name; sti_type; sti_loc } : ParserAST.static_typed_ident =
  let sti_name = cvt_ident sti_name in
  let sti_type = relocalize_fun static_type_to_string sti_type in
  ParserAST.{ sti_name; sti_type; sti_loc }

let cvt_typed_ident { ti_name; ti_type; ti_loc } : ParserAST.typed_ident =
  let ti_type = relocalize_fun cvt_global_type ti_type in
  ParserAST.{ ti_name = cvt_ident ti_name;
              ti_type; ti_loc }

(* remove size from lvalue *)

let rec cvt_lvalue_desc lv : ParserAST.lvalue_desc =
  match lv with
  | LValDrop -> LValDrop
  | LValId id -> LValId (cvt_ident id)
  | LValTuple lvs -> LValTuple (List.map cvt_lvalue lvs)

and cvt_lvalue (lv:lvalue) : ParserAST.lvalue =
  relocalize lv.b_loc @@ cvt_lvalue_desc lv.b_desc

(* convert expressions *)

let rec cvt_exp_desc (e:exp_desc) : ParserAST.exp_desc =
  match e with
  | EConst v -> EConst v
  | EVar id -> EVar (cvt_ident id)
  | EReg e -> EReg (cvt_exp e)
  | ECall (fname, ps, args) ->
     ECall (fname,
            List.map cvt_opt_static_bitype_exp ps,
            List.map cvt_exp args)
  | EMem (kd, (a, w, f), args) ->
     EMem (kd, (cvt_opt_static_int_exp a, cvt_opt_static_int_exp w, f),
           List.map cvt_exp args)

and cvt_exp (e:exp) = relocalize !$@e @@ cvt_exp_desc !$!e

let cvt_state_exp_desc : 'a -> ParserAST.exp_desc = function
  | EConstr c -> EConstr (cvt_ident c)

let cvt_state_exp (e:state_exp) = relocalize e.s_loc @@ cvt_state_exp_desc e.s_desc

let cvt_state_transition_exp_desc : state_transition_exp_desc -> ParserAST.exp_desc = function
  | EContinue e -> EContinue (cvt_state_exp e)
  | ERestart e ->  ERestart (cvt_state_exp e)

let cvt_state_transition_exp (e:state_transition_exp) = relocalize e.st_loc @@ cvt_state_transition_exp_desc e.st_desc

let cvt_tritype_exp = function
  | Exp e -> cvt_exp e
  | StateExp e -> cvt_state_exp e
  | StateTransitionExp e -> cvt_state_transition_exp e

(* convert automaton/match handler *)

let rec cvt_match_hdl { m_state; m_hloc; m_body } : ParserAST.match_handler =
  { m_state = cvt_ident m_state; m_hloc; m_body = cvt_block m_body}

and cvt_match { m_handlers; m_loc; _ } : ParserAST.matcher =
  { m_handlers = m_handlers |> ConstructEnv.to_seq |> List.of_seq |> List.map snd |> List.map cvt_match_hdl; m_loc }

and cvt_transition (e1, e2) =
  cvt_exp e1, cvt_state_transition_exp e2

and cvt_automaton_hdl { a_state; a_hloc; a_body; a_weak_transition; a_strong_transition } : ParserAST.automaton_handler =
  { a_state  = cvt_ident a_state;
    a_hloc;
    a_body   = cvt_block a_body;
    a_weak_transition   = List.map cvt_transition a_weak_transition;
    a_strong_transition = List.map cvt_transition a_strong_transition }

and cvt_automaton { a_handlers; a_loc; a_fst_state; _ } : ParserAST.automaton =
  let a_handlers = a_handlers |> ConstructEnv.to_seq |> List.of_seq |> List.map snd |> List.map cvt_automaton_hdl in
  let a_handlers = (fun (a, b) -> a @ b) @@ List.partition (fun hdl -> !!(hdl.ParserAST.a_state) = a_fst_state.id_desc) a_handlers in
  { a_handlers; a_loc }


(* convert declarations *)

and cvt_decl_desc (d:decl_desc) : ParserAST.decl_desc =
  match d with
  | Deq (lv, e) -> Deq (cvt_lvalue lv, cvt_tritype_exp e)
  | Dlocaleq (lv, e) -> Dlocaleq (cvt_lvalue lv, cvt_tritype_exp e)
  | Dreset (e, eqs) -> Dreset (cvt_exp e, cvt_block eqs)
  | Dautomaton a -> Dautomaton (cvt_automaton a)
  | Dmatch (e, m) -> Dmatch (cvt_state_exp e, cvt_match m)
  | Dif (c, b1, b2) ->
    Dif (cvt_static_bool_exp c, cvt_block b1, cvt_block b2)

and cvt_decl (d:decl) : ParserAST.decl = relocalize !@d @@ cvt_decl_desc !!d

and cvt_block (ds: decl list) : ParserAST.decl list = List.map cvt_decl ds
(* convert nodes *)

let cvt_node _ node lst: ParserAST.node list =
  let n: ParserAST.node =
    { node_name    = node.node_name;
      node_loc     = node.node_loc;
      node_inline  = node.node_inline;
      node_inputs  = List.map cvt_typed_ident node.node_inputs;
      node_outputs = List.map cvt_typed_ident node.node_outputs;
      node_params  = List.map cvt_static_typed_ident node.node_params;
      node_body    = relocalize node.node_loc @@ cvt_block node.node_body;
      node_probes  = [] (* They are lost *) } in
  n :: lst

let cvt_const _ const lst: ParserAST.const list =
  let c: ParserAST.const =
    { const_left  = cvt_ident const.const_name;
      const_right = cvt_static_bitype_exp const.const_decl;
      const_loc = const.const_loc } in
  c :: lst

let cvt_enum _ enum lst: ParserAST.enum list =
  let e: ParserAST.enum =
    { enum_name   = cvt_ident enum.enum_name;
      enum_constructors = List.map cvt_ident enum.enum_constructors_names;
      enum_loc = enum.enum_loc } in
  e :: lst

let program p: ParserAST.program =
  { p_enums = List.sort_uniq (compare) @@ ConstructEnv.fold cvt_enum p.p_enums [];
    p_consts = Env.fold cvt_const p.p_consts [];
    p_nodes = FunEnv.fold cvt_node p.p_nodes [] }

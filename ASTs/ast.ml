open CommonAST

(** All static typing/processing is done
    no more locations since we can't fail now *)

type netlist_type =
  | TBit
  | TBitArray of int
  | TProd of netlist_type list

type 'a typed = { desc: 'a; typ: netlist_type }

type value =
  | VNDim of value list
  | VBit of bool

type slice_param = int * int

type lvalue =
  | LValDrop
  | LValId of ident
  | LValTuple of lvalue list

type 'e state_expr =
  | Estate0 of ident
  | Estaten of ident * 'e list

type state =
  | Estate0pat of ident
  | Estatenpat of ident * ident list

let state_name = function
  | Estate0pat id -> id
  | Estatenpat (id, _) -> id

type ('e, 'b) match_hdl = {
    m_constr: constructor;
    m_body: 'b
  }

type ('e, 'b) escape = {
    e_cond: 'e;
    e_reset: bool;
    e_body: 'b;
    e_nx_state: 'e state_expr
  }

type ('e, 'b) automaton_hdl = {
    s_state: state;
    s_vars: ident list;
    s_body: 'b;
    s_trans: ('e, 'b) escape list;
  }

type is_weak = bool

type exp_desc =
  | EConst  of value
  | EConstr of exp state_expr
  | EVar    of ident
  | EReg    of exp
  | ESupOp  of name * exp list
  | ESlice  of slice_param list * exp
  | ECall   of ident * exp list
  | EMem    of mem_kind * (int * int * name option) * exp list
  | ELet    of decl * exp
  | EMerge  of exp * (exp, decl) match_hdl list
  | EMatch  of exp * (exp, decl) match_hdl list
and exp = exp_desc typed

and decl_desc =
  | Dempty
  | Deq        of lvalue * exp (* p = e *)
  | Dand       of decl list (* eq1; ... ; eqn *)
  | Dlet       of decl * decl (* let eq in eq *)
  | Dreset     of decl * exp (* reset eq every e *)
  | Dautomaton of is_weak * (exp, decl) automaton_hdl list
and decl = decl_desc typed

type node = {
    node_name:    ident;
    node_inline:  inline_status;
    node_inputs : ident typed list;
    node_outputs: ident typed list;
    node_body:    decl;
    node_probes : ident list;
  }

type program = node list

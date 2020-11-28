open Ast
module StaticScopingAST = Static_scoping.StaticScopingAST
exception Scoping_error of string * Location.location

module StaticConstrainingAST = struct
  type sunop = ParsingAST.sunop
  type sop = ParsingAST.sop

  type static_exp_desc =
    | SInt   of int
    | SBool  of bool
    | SParam of int
    | SConst of ident
    | SUnOp  of      sunop * static_exp
    | SBinOp of        sop * static_exp * static_exp
    | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

  and static_exp = static_exp_desc static_constrained


  and static_constraints =
    | CParam of    int
    | CConstant of ident
    | CUnoparg of  sunop
    | CUnopres of  sunop
    | CBinoparg of sop
    | CBinopres of sop
    | CCondition
    | CThenElse of static_exp
    
  and 'a static_constrained =
    {
      st_desc: 'a;
      st_loc: Location.location;
      st_constraints: static_constraints list
    }

  let (!$!) = fun obj -> obj.st_desc
  let (!$~) = fun obj -> obj.st_constraints
  let (!$@) = fun obj -> obj.st_loc

  let static_constrain desc loc constraints = {
    st_desc = desc;
    st_constraints = constraints;
    st_loc = loc
  }
  
  let static_constrain_same { desc; loc } constraints = static_constrain desc loc constraints


  type optional_static_exp_desc = static_exp_desc option
  and optional_static_exp = optional_static_exp_desc static_constrained

  (* Netlist expressions *)

  type netlist_type =
    | TBitArray of optional_static_exp
    | TProd of netlist_type list


  type exp_desc =
    | EConst of ParsingAST.value
    | EVar   of ident
    | EReg   of exp
    | ECall  of ident * optional_static_exp list * exp list
        (* function * params * args *)
    | EMem   of ParsingAST.mem_kind * (static_exp * static_exp * string option) * exp list
        (* ro * (address size * word size * input file) * args *)

  and exp = exp_desc localized

  type equation_desc = {
    eq_left:  ParsingAST.lvalue;
    eq_right: exp
  }
  and equation = equation_desc localized


  type typed_ident_desc = {
    name:  ident;
    typed: netlist_type localized;
  }
  and typed_ident = typed_ident_desc localized


  type block_desc =
    | BEqs of equation list
    | BIf  of static_exp * block * block

  and block = block_desc localized

  type node = {
    node_name_loc:  Location.location;
    node_loc:       Location.location;
    node_params:    ParsingAST.static_typed_ident list;
    node_inline:    ParsingAST.inline_status;
    node_inputs:    typed_ident list;
    node_outputs:   typed_ident list;
    node_body:      block;
    node_probes:    ident list;
  }

  type const = {
    const_decl:   static_exp;
    const_idents: Location.location;
    const_totals: Location.location;
  }

  type program = {
    p_consts: const Env.t;
    p_nodes:  node  Env.t;
  }
end
open StaticConstrainingAST

let rec constrain_static_exp ?(constraints=[]) (st_exp: StaticScopingAST.static_exp):
  static_exp_desc static_constrained =

  match !!st_exp with
    | SInt n ->
        static_constrain (SInt n) !@st_exp constraints
    | SBool b ->
        static_constrain (SBool b) !@st_exp constraints
    | SParam nb ->
        static_constrain (SParam nb) !@st_exp (CParam nb :: constraints)
    | SConst id ->
        static_constrain (SConst id) !@st_exp (CConstant id :: constraints)
    | SUnOp (unop, e) ->
        let constrained = constrain_static_exp e ~constraints:[CUnoparg unop] in
        static_constrain (SUnOp (unop, constrained)) !@st_exp (CUnopres unop :: constraints)
    | SBinOp (op, e1, e2) ->
        let constrained1 = constrain_static_exp e1 ~constraints:[CBinoparg op] in
        let constrained2 = constrain_static_exp e2 ~constraints:[CBinoparg op] in
        static_constrain (SBinOp (op, constrained1, constrained2)) !@st_exp (CBinopres op :: constraints)
    | SIf (eb, e1, e2) ->
        let constrainedb = constrain_static_exp eb ~constraints:[CCondition] in
        let constrained1 = constrain_static_exp e1 ~constraints:[] in
        let constrained2 = constrain_static_exp e2 ~constraints:[CThenElse constrained1] in
        static_constrain (SIf (constrainedb, constrained1, constrained2)) !@st_exp (CThenElse constrained1 :: constraints)



let constrain_optional_static_exp e = match !!e with
  | None -> static_constrain None !@e []
  | Some ed ->
      let res = constrain_static_exp (relocalize !@e ed) in
      { res with st_desc = Some !$!res }


let rec constrain_exp e = match !!e with
  | StaticScopingAST.EConst c ->  relocalize !@e (EConst c)
  | StaticScopingAST.EVar id ->   relocalize !@e (EVar id)
  | StaticScopingAST.EReg e ->    relocalize !@e (EReg (constrain_exp e))
  | StaticScopingAST.ECall (fname, params, args) ->
                                  relocalize !@e (ECall (fname, List.map constrain_optional_static_exp params, List.map constrain_exp args))
  | StaticScopingAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
                                  relocalize !@e (EMem (mem_kind, (constrain_static_exp addr_size, constrain_static_exp word_size, input_file),
                                                        List.map constrain_exp args))

let constrain_eq = relocalize_fun (fun StaticScopingAST.{ eq_left; eq_right } ->
  { eq_left; eq_right = constrain_exp eq_right }
)

let rec constrain_body e = relocalize_fun (function
  | StaticScopingAST.BIf (condition, block1, block2) -> BIf (constrain_static_exp condition, constrain_body block1, constrain_body block2)
  | StaticScopingAST.BEqs eq_l -> BEqs (List.map constrain_eq eq_l)
  ) e

let constrain_starput = relocalize_fun (fun StaticScopingAST.{ name; typed } ->
  let rec constrain_typed = function
    | StaticScopingAST.TProd l ->     TProd (List.map constrain_typed l)
    | StaticScopingAST.TBitArray e -> TBitArray (constrain_optional_static_exp e)
  in
  { name; typed = relocalize_fun constrain_typed typed }
)

let constrain_node StaticScopingAST.{ node_name_loc; node_loc; node_inline; node_inputs; node_outputs; node_params; node_body; node_probes } =
  {
    node_inputs =   List.map constrain_starput node_inputs;
    node_outputs =  List.map constrain_starput node_outputs;
    node_body =     constrain_body node_body;
    node_name_loc; node_loc; node_inline; node_params; node_probes
  }

let constrain_const StaticScopingAST.{ const_decl; const_idents; const_totals } =
  {
    const_decl = constrain_static_exp const_decl;
    const_idents; const_totals
  }

let program StaticScopingAST.{ p_consts; p_nodes } : program =
  {
    p_consts = Env.map constrain_const p_consts;
    p_nodes = Env.map constrain_node p_nodes;
  }

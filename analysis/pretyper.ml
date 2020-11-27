open Ast

module PreTypingAST = struct


  type static_exp_desc = (* Removed SPar *)
    | SInt   of int
    | SBool  of bool
    | SConst of ident
    | SUnOp  of ParsingAST.sunop * static_exp
    | SBinOp of ParsingAST.  sop * static_exp * static_exp
    | SIf    of       static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

  and static_exp = static_exp_desc localized

  type optional_static_exp_desc = static_exp_desc option
  and optional_static_exp = optional_static_exp_desc localized

  (* Netlist expressions *)

  type netlist_type =
    | TBitArray of optional_static_exp
    | TProd of netlist_type list


  type exp_desc = (* Removed EPar *)
    | EConst of ParsingAST.value
    | EVar   of ident
    | EReg   of exp
    | ECall  of ident * optional_static_exp list * exp list
        (* function * params * args *)
    | EMem   of ParsingAST.mem_kind * (static_exp * static_exp * string option) * exp list
        (* ro * address size * word size * input file * args *)

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

  type node_desc = {
    node_name_loc:  Location.location;
    node_loc:       Location.location;
    node_params:    ParsingAST.static_typed_ident list;
    node_inline:    ParsingAST.inline_status;
    node_inputs:    typed_ident list;
    node_outputs:   typed_ident list;
    node_body:      block;
    node_probes:    ident list;
  }
  and node = node_desc localized

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
open ParsingAST
open PreTypingAST

let relocalize_fun f obj =
  relocalize !@obj (f !!obj)



let rec static_exp se = match !!se with
  | ParsingAST.SInt n ->                  relocalize !@se (SInt n)
  | ParsingAST.SBool b ->                 relocalize !@se (SBool b)
  | ParsingAST.SConst id ->               relocalize !@se (SConst id)
  | ParsingAST.SPar e ->                  static_exp e
  | ParsingAST.SUnOp (sunop, se1) ->      relocalize !@se (SUnOp (sunop, static_exp se1))
  | ParsingAST.SBinOp (sop, se1, se2) ->  relocalize !@se (SBinOp (sop, static_exp se1, static_exp se2))
  | ParsingAST.SIf (seb, se1, se2) ->     relocalize !@se (SIf (static_exp seb, static_exp se1, static_exp se2))

let optional_static_exp e = match !!e with
  | None -> relocalize !@e None
  | Some ed ->
      let res = static_exp (relocalize !@e ed) in
      relocalize !@res (Some !!res)


let rec exp e = match !!e with
  | ParsingAST.EConst c ->  relocalize !@e (EConst c)
  | ParsingAST.EVar id ->   relocalize !@e (EVar id)
  | ParsingAST.EPar e ->    exp e
  | ParsingAST.EReg e ->    relocalize !@e (EReg (exp e))
  | ParsingAST.ECall (fname, params, args) ->
                            relocalize !@e (ECall (fname, List.map optional_static_exp params, List.map exp args))
  | ParsingAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
                            relocalize !@e (EMem (mem_kind, (static_exp addr_size, static_exp word_size, input_file), List.map exp args))

let eq = relocalize_fun (fun ParsingAST.{ eq_left; eq_right } ->
  { eq_left; eq_right = exp eq_right }
)

let rec body e = relocalize_fun (function
  | ParsingAST.BIf (condition, block1, block2) -> BIf (static_exp condition, body block1, body block2)
  | ParsingAST.BEqs eq_l -> BEqs (List.map eq eq_l)
  ) e

let starput = relocalize_fun (fun ParsingAST.{ name; typed } ->
  let rec fun_typed : ParsingAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_typed l)
    | TBitArray e -> TBitArray (optional_static_exp e)
  in
  { name; typed = relocalize_fun fun_typed typed }
)

let node (node: ParsingAST.node) : node =
  let { node_name; node_inline; node_inputs; node_outputs; node_params; node_body; node_probes } = !!node in
  relocalize !@node {
    node_name_loc = !@node_name;
    node_loc =      !@node;
    node_inputs =   List.map starput node_inputs;
    node_outputs =  List.map starput node_outputs;
    node_body =     body node_body;
    node_inline; node_params; node_probes
  }

let const const =
  let { const_left; const_right } = !!const in
  {
    const_decl =   static_exp const_right;
    const_idents = !@const_left;
    const_totals = !@const
  }

let program ParsingAST.{ p_consts; p_nodes } : program =
  { p_consts = List.fold_left
    (fun env const_ ->
      Env.add !!ParsingAST.(!!const_.const_left) (const const_) env
    ) Env.empty p_consts;
    p_nodes = List.fold_left
    (fun env node_ ->
      Env.add !!ParsingAST.(!!node_.node_name) (node node_) env
    ) Env.empty p_nodes;
  }
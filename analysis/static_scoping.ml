open Ast

module StaticScopedAST = struct
  type sunop = ParsingAST.sunop
  type sop = ParsingAST.sop

  type static_exp_desc = (* Removed SPar *)
    | SInt   of int
    | SBool  of bool
    | SConst of ident
    | SParam of int
    | SUnOp  of      sunop * static_exp
    | SBinOp of        sop * static_exp * static_exp
    | SIf    of static_exp * static_exp * static_exp  (* se1 ? se2 : se3 *)

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
    const_ident: Location.location;
    const_total: Location.location;
  }

  type program = {
    p_consts: const Env.t;
    p_consts_order: ident_desc list;
    p_nodes:  node  Env.t;
  }

end
open ParsingAST
open StaticScopedAST


let static_exp consts_set ?(params_order=Env.empty) =
  let rec f se = match !!se with
    | ParsingAST.SInt n ->                  relocalize !@se (SInt n)
    | ParsingAST.SBool b ->                 relocalize !@se (SBool b)
    | ParsingAST.SIdent id ->               relocalize !@se (
                                              if Env.mem !!id params_order then
                                                SParam (Env.find !!id params_order)
                                              else if IdentSet.mem !!id consts_set then
                                                SConst id
                                              else
                                                raise (Errors.Scoping_error (!!id, !@id))
                                            )
    | ParsingAST.SPar e ->                  f e
    | ParsingAST.SUnOp (sunop, se1) ->      relocalize !@se (SUnOp (sunop, f se1))
    | ParsingAST.SBinOp (sop, se1, se2) ->  relocalize !@se (SBinOp (sop, f se1, f se2))
    | ParsingAST.SIf (seb, se1, se2) ->     relocalize !@se (SIf (f seb, f se1, f se2))
  in f
let static_exp_full (consts_set, params_order) = static_exp consts_set ~params_order

let optional_static_exp env e = match !!e with
  | None -> relocalize !@e None
  | Some ed ->
      let res = static_exp_full env (relocalize !@e ed) in
      relocalize !@res (Some !!res)


let rec exp env e = match !!e with
  | ParsingAST.EConst c ->  relocalize !@e (EConst c)
  | ParsingAST.EVar id ->   relocalize !@e (EVar id)
  | ParsingAST.EPar e ->    exp env e
  | ParsingAST.EReg e ->    relocalize !@e (EReg (exp env e))
  | ParsingAST.ECall (fname, params, args) ->
                            relocalize !@e (ECall (fname, List.map (optional_static_exp env) params, List.map (exp env) args))
  | ParsingAST.EMem (mem_kind, (addr_size, word_size, input_file), args) ->
                            relocalize !@e (EMem (mem_kind, (static_exp_full env addr_size, static_exp_full env word_size, input_file), List.map (exp env) args))

let eq env = relocalize_fun (fun ParsingAST.{ eq_left; eq_right } ->
  { eq_left; eq_right = exp env eq_right }
)

let rec body env e = relocalize_fun (function
  | ParsingAST.BIf (condition, block1, block2) -> BIf (static_exp_full env condition, body env block1, body env block2)
  | ParsingAST.BEqs eq_l -> BEqs (List.map (eq env) eq_l)
  ) e

let starput env = relocalize_fun (fun ParsingAST.{ name; typed } ->
  let rec fun_typed : ParsingAST.netlist_type -> 'a = function
    | TProd l -> TProd (List.map fun_typed l)
    | TBitArray e -> TBitArray (optional_static_exp env e)
  in
  { name; typed = relocalize_fun fun_typed typed }
)

let node consts_set (node: ParsingAST.node) : node =
  let { node_name; node_inline; node_inputs; node_outputs; node_params; node_body; node_probes } = !!node in
  let params_order = Misc.fold_lefti (fun env i el -> Env.add !!(!!el.st_name) i env) Env.empty node_params in
  {
    node_name_loc = !@node_name;
    node_loc =      !@node;
    node_inputs =   List.map (starput (consts_set, params_order)) node_inputs;
    node_outputs =  List.map (starput (consts_set, params_order)) node_outputs;
    node_body =     body (consts_set, params_order) node_body;
    node_inline; node_params; node_probes
  }

let const consts_set const =
  let { const_left; const_right } = !!const in
  {
    const_decl =  static_exp consts_set const_right;
    const_ident = !@const_left;
    const_total = !@const
  }

let program ParsingAST.{ p_consts; p_nodes } : program =
  let consts_set = List.fold_left (fun set el -> IdentSet.add !!(!!el.const_left) set) IdentSet.empty p_consts in
  { p_consts = List.fold_left
    (fun env const_ ->
      Env.add !!(!!const_.const_left) (const consts_set const_) env
    ) Env.empty p_consts;
    p_consts_order = List.map (fun el -> !!(!!el.const_left)) p_consts;
    p_nodes = List.fold_left
    (fun env node_ ->
      Env.add !!ParsingAST.(!!node_.node_name) (node consts_set node_) env
    ) Env.empty p_nodes;
  }
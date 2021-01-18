open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let zero = { si_desc = EConst (VBit false);
             si_loc = Location.no_location;
             si_size = TNDim [] }

let rst (c:exp) (exp:tritype_exp) =
  match exp with
  | Exp e ->
     let si_desc = ECall (relocalize e.si_loc "mux", [], [c; e; zero]) in
     Exp { e with si_desc }
  | StateExp e -> StateExp { e with s_desc = ESReg e }
  | StateTransitionExp _ -> assert false

let mk_or (c1:exp) (c2:exp) =
  { c1 with si_desc = ECall (relocalize c1.si_loc "or", [], [c1; c2]) }

let rst_node_tbl : (string, node) Hashtbl.t = Hashtbl.create 16
let rst_program = ref { p_enums = ConstructEnv.empty;
                        p_consts = Env.empty;
                        p_consts_order = [];
                        p_nodes = FunEnv.empty }
let is_native_fname s =
  let regex = Str.regexp {|\(or\|and\|xor\|nand\|nor\|not\|mux\)_\([01]\)|} in
  Str.string_match regex s 0

let rec rst_node (n:node) =
  let id_rst = identify n.node_loc "rst" (UIDIdent.get ()) in
  let ti_rst = { ti_name = id_rst;
                 ti_type = relocalize n.node_loc (BNetlist (TNDim []));
                 ti_loc  = n.node_loc } in
  let var_rst = size (EVar id_rst) n.node_loc (TNDim []) in
  let n_rst =
    { n with
      node_name = relocalize n.node_name.loc @@ "rst_" ^ n.node_name.desc;
      node_inputs = ti_rst :: n.node_inputs;
      node_body = List.concat_map (decl (Some var_rst)) n.node_body }
  in
  Hashtbl.replace rst_node_tbl n.node_name.desc n_rst;
  n_rst.node_name

and exp (c:exp) (e:tritype_exp) = match e with
  | Exp e -> Exp (exp_aux c e)
  | _ -> e

and exp_aux (c:exp) (e:exp) = match e.si_desc with
  | ECall ({ desc = fname; _ }, _, _) when is_native_fname fname -> e
  | ECall ({ desc = "slice_one"; _ }, _, _)
    | ECall ({ desc = "slice_all"; _ }, _, _)
    | ECall ({ desc = "slice_from"; _ }, _, _)
    | ECall ({ desc = "slice_to"; _ }, _, _)
    | ECall ({ desc = "slice_fromto"; _ }, _, _)
    | ECall ({ desc = "add_dim_0"; _ }, _, _)
    | ECall ({ desc = "concat_1"; _ }, _, _)  -> e

  | ECall(fname, ps, args) ->
     let rst_fname = match Hashtbl.find_opt rst_node_tbl fname.desc with
       | Some n -> n.node_name
       | None -> rst_node (FunEnv.find fname.desc (!rst_program).p_nodes)
     in
     { e with si_desc = ECall (rst_fname, ps, c :: args) }

  | _ -> e


and decl (c:exp option) (d:decl) : decl list = match d.desc with
  | Deq (lv, e) ->
     begin match c with
     | None -> [d]
     | Some c -> [{ d with desc = Deq (lv, rst c (exp c e))}]
     end
  | Dreset (e, ds) ->
     begin match c with
     | None   -> List.concat_map (decl (Some e)) ds
     | Some c -> List.concat_map (decl (Some (mk_or c e))) ds
     end
  | Dif (g, b1, b2) ->
     let b1 = List.concat_map (decl c) b1 in
     let b2 = List.concat_map (decl c) b2 in
     [{ d with desc = Dif (g, b1, b2)}]
  | Dmatch (e, m) ->
     let m_handlers =
       ConstructEnv.map
         (fun h -> { h with m_body = List.concat_map (decl c) h.m_body })
         m.m_handlers in
     [relocalize d.loc @@ Dmatch (e, { m with m_handlers })]

  | Dlocaleq (_, _) -> assert false
  | Dautomaton _ -> assert false

let node (n:node) = { n with node_body = List.concat_map (decl None) n.node_body }

(** [Reset.program p] produce a program with
    no automaton and produces a program
    with no resets *)
let program (p:program) =
  rst_program := p;
  let p_nodes = FunEnv.map node p.p_nodes in
  let p_nodes =
    Hashtbl.fold (fun _ n p_nodes -> FunEnv.add n.node_name.desc n p_nodes)
      rst_node_tbl p_nodes in
  { p with p_nodes }

open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let zero = { si_desc = EConst (VBit false);
             si_loc = Location.no_location;
             si_size = TNDim [Size (SInt 1)]}

let rst (c:exp) (exp:tritype_exp) =
  match exp with
  | Exp e ->
     let si_desc = ECall (relocalize e.si_loc "mux", [], [c; zero; e]) in
     Exp { e with si_desc }
  | StateExp e -> StateExp { e with s_desc = ESReg e }
  | StateTransitionExp _ -> assert false

let mk_or (c1:exp) (c2:exp) =
  { c1 with si_desc = ECall (relocalize c1.si_loc "or", [], [c1; c2]) }

let fmap f lst = List.flatten @@ List.map f lst

let rec decl (c:exp option) (d:decl) : decl list = match d.desc with
  | Deq (lv, e) ->
     begin match c with
     | None -> [d]
     | Some c -> [{ d with desc = Deq (lv, rst c e)}]
     end
  | Dreset (e, ds) ->
     begin match c with
     | None   -> fmap (decl (Some e)) ds
     | Some c -> fmap (decl (Some (mk_or c e))) ds
     end
  | Dif (g, b1, b2) ->
     let b1 = fmap (decl c) b1 in
     let b2 = fmap (decl c) b2 in
     [{ d with desc = Dif (g, b1, b2)}]
  | Dmatch (e, m) ->
     let m_handlers =
       ConstructEnv.map
         (fun h -> { h with m_body = fmap (decl c) h.m_body })
         m.m_handlers in
     [relocalize d.loc @@ Dmatch (e, { m with m_handlers })]

  | Dlocaleq (_, _) -> assert false
  | Dautomaton _ -> assert false

let node (n:node) = { n with node_body = fmap (decl None) n.node_body }

(** [Reset.program p] produce a program with
    no automaton and produces a program
    with no resets *)
let program (p:program) = { p with p_nodes = FunEnv.map node p.p_nodes }

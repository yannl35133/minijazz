open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

let zero = { si_desc = EConst (VBit false);
             si_loc = Location.no_location;
             si_size = TNDim [Size (SInt 1)]}

let rst (c:exp) (e:exp) =
  { e with si_desc = ECall (relocalize e.si_loc "mux", [], [c; zero; e]) }

let mk_or (c1:exp) (c2:exp) =
  { c1 with si_desc = ECall (relocalize c1.si_loc "or", [], [c1; c2]) }

let rec decl (c:exp option) (d:decl) : decl list = match d.desc with
  | Deq (lv, e) ->
     let e = match e with
       | Exp e -> e
       | StateExp _ -> assert false
       | StateTransitionExp _ -> assert false in
     begin match c with
     | None -> [d]
     | Some c -> [{ d with desc = Deq (lv, Exp (rst c e))}]
     end
  | Dreset (e, ds) ->
     begin match c with
     | None -> List.flatten @@ List.map (decl (Some e)) ds
     | Some c -> List.flatten @@ List.map (decl (Some (mk_or c e))) ds
     end
  | Dif (g, b1, b2) ->
     let b1 = List.flatten @@ List.map (decl c) b1 in
     let b2 = List.flatten @@ List.map (decl c) b2 in
     [{ d with desc = Dif (g, b1, b2)}]

  | Dlocaleq (_, _) -> assert false
  | Dautomaton _ -> assert false
  | Dmatch (_, _) -> assert false

let node (n:node) = { n with node_body = List.map (decl None) n.node_body }

(** [Reset.program p] produce a program with
    no automaton nor match and produces a program
    with no resets *)
let program (p:program) = { p with p_nodes = FunEnv.map node p.p_nodes }
open CommonAST
open StaticTypedPartialAST
open NetlistSizedAST

(* some utilitary functions to write code *)

let var name loc ty = size (EVar name) loc ty

let reg (e:exp) = { e with s_desc = EReg e }

let eq v (e:exp) =
  match v.s_desc with
  | EVar id -> relocalize id.loc @@ Deq ({ v with s_desc = LValId id } , e)
  | _ -> assert false

let mtch e hdls = relocalize e.s_loc @@ Dmatch (e, hdls)

(* list of all new enums introduced during reduction *)
let enums = ref []

(* clean workspace
   dont forget before start reduction ! *)
let clean () = enums := []

let prefix p id = relocalize !@id @@ p ^ !!id

(** [new_enum constructors] introduce a fresh enum type and return a pair
    prefix of state names in constructors and enum type name *)
let new_enum names =
  let id = UniqueId.get () in
  let p = ("_S"^(UniqueId.to_string id)) in
  let name = "enum" ^ (UniqueId.to_string id) in
  let enum =
    { enum_name = no_localize @@ name;
      enum_pats = List.map (prefix p) names;
      enum_loc  = Location.no_location }
  in
  enums := enum :: !enums;
  p, name

(** [new_var prefix location ty] introduce a fresh variable *)
let new_var ty p loc =
  let id = UniqueId.get () in
  let name = { loc; desc = (p ^ (UniqueId.to_string id)) } in
  var name loc ty

let one_bit_type = TDim [Size (SInt 1)]
let tmp_type = one_bit_type (* TODO replace with enum type*)

(* one bit type variable *)
let new_bvar = new_var one_bit_type
let new_evar _enum = new_var tmp_type (* TODO *)

(** [automaton_reduction p] takes a program and
    transform the ast in order to remove all automaton constructions *)

(* associate constructor name with the corresponding state variable name
   returns the _next state_ variable, the one match at next cycle *)
let automaton_tbl : (string, exp) Hashtbl.t = Hashtbl.create 16

let add_enum vars constructors =
  List.iter (fun c -> Hashtbl.replace automaton_tbl c.desc vars) constructors

let rec auto_decl_red_desc (d:decl) = match d.desc with
  | Dautomaton hdls ->
     (* produce enum for state variable *)
     let states = List.map (fun hdl -> hdl.s_state) hdls in
     let p, enum_ty = new_enum states in

     (* state variables *)
     let st = new_evar enum_ty ("cur_state"^p) d.loc in
     let nx_st = new_evar enum_ty ("nx_state"^p) d.loc in
     add_enum nx_st states;

     (* create match handlers *)
     let hdl_red hdl =
       (* each body is wrapped into a reset with its own variable *)
       let reset = new_bvar ("rst"^p^hdl.s_state.desc) hdl.s_state.loc in
       let body = Dreset (auto_decl_red hdl.s_body, reset) in

       (* TODO escapes *)

       { m_constr = prefix p hdl.s_state;
         m_body = relocalize hdl.s_body.loc body }
     in

     let hdls = List.map hdl_red hdls in

     (* [st = reg(nx_st)] *)
     let st_eq = eq st (reg nx_st) in
     Dblock [st_eq; mtch st hdls]
  | d -> d

and auto_decl_red d = { d with desc = auto_decl_red_desc d }

let auto_node_reduction n =
  { n with node_body = auto_decl_red n.node_body}

let automaton_reduction (p:program) =
  clean ();
  Hashtbl.clear automaton_tbl;
  let p_nodes = Env.map auto_node_reduction p.p_nodes in
  { p with p_nodes }

(** [match_reduction p] takes a program and
    transform the ast in order to remove all match constructions
    here we assume no automaton are left *)
let match_reduction (_p:program) = assert false

(** [reset_reduction p] takes a program and
    transform the ast in order to remove all reset constructions
    here we assume no automaton nor match are left *)
let reset_reduction (_p:program) = assert false

open Netlist_ast

type var_rep =
    | EnCours
    | Keep
    | Replaced  of arg

let simplify : program -> program
= fun prg ->
    let eq_ev = Env.of_list prg.p_eqs in (*TODO: outputs=const*)
    let rec find_rep rep (v_n, exp) =
        try match Env.find v_n rep with
            | EnCours -> raise Scheduler.Combinational_cycle
            | Replaced u -> rep, u
            | Keep -> rep, Avar v_n
        with Not_found ->
            match exp with
            | Earg (Avar u_n as u) ->
                begin try let u_eq = Env.find u_n eq_ev
                in let rep = Env.add v_n EnCours rep
                in let rep, u_r = find_rep rep (u_n, u_eq)
                in Env.add v_n (Replaced u_r) rep, u_r
                with Not_found 
                    -> Env.add v_n (Replaced u) rep, u
                end
            | Earg (Aconst _ as c) ->
                    Env.add v_n (Replaced c) rep, c
            | _ -> Env.add v_n Keep rep, Avar v_n
    in let rep = List.fold_left (fun rep eq -> fst (find_rep rep eq))
                    Env.empty prg.p_eqs
    in let keep_v v_n =
        try match Env.find v_n rep with
            | Replaced u -> false | _ -> true
        with Not_found -> true
    in let repl_v v_n =
        try match Env.find v_n rep with
            | Replaced u -> u | _ -> Avar v_n
        with Not_found -> Avar v_n
    in let repl = function
        | Avar v -> repl_v v
        | Aconst c -> Aconst c
    in let fold_eq rt (v_n, exp) =
        match exp with 
        | Earg a -> rt
        | Ereg v -> begin match repl_v v with
                    | Aconst _ as c -> (v_n, Earg c)::rt
                    | Avar u_n -> (v_n, Ereg u_n)::rt
                    end
        | Enot a -> (v_n,Enot (repl a))::rt
        | Ebinop (b,a1,a2) -> (v_n,Ebinop (b,repl a1,repl a2))::rt
        | Emux (a1,a2,a3) -> (v_n,Emux (repl a1,repl a2,repl a3))::rt
        | Erom (i,j,a) -> (v_n,Erom (i,j,repl a))::rt
        | Eram (i,j,a1,a2,a3,a4) 
            -> (v_n,Eram (i,j,repl a1,repl a2,repl a3,repl a4))::rt
        | Econcat (a1,a2) -> (v_n,Econcat (repl a1,repl a2))::rt
        | Eslice (i,j,a) -> (v_n,Eslice (i,j,repl a))::rt
        | Eselect (i,a) -> (v_n,Eselect (i,repl a))::rt
    in let p_outputs, ocst_eqs = List.fold_right
        (fun v_n (p_o, o_c) ->
            match repl_v v_n with
            | Avar u_n -> u_n::p_o, o_c
            | Aconst _ as c -> v_n::p_o, (v_n, Earg c)::o_c
        ) prg.p_outputs ([],[])
    in {
        p_eqs = List.rev (ocst_eqs @ (List.fold_left fold_eq [] prg.p_eqs));
        p_inputs = prg.p_inputs;
        p_outputs;
        p_vars = Env.filter (fun v_n _ -> keep_v v_n) prg.p_vars
    }

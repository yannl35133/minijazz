open Netlist_ast

type var_rep =
    | EnCours
    | Keep
    | Replaced  of arg

let simplify : program -> program
= fun prg ->
    let eq_ev = Env.of_list prg.p_eqs in
    let rec find_rep rep (v_n, exp) =
        let find_aux rep u_n =
            try let u_eq = Env.find u_n eq_ev 
                in find_rep rep (u_n, u_eq)
            with Not_found -> rep, Avar u_n
        in try match Env.find v_n rep with
            | EnCours -> raise Scheduler.Combinational_cycle
            | Replaced u -> rep, u
            | Keep -> rep, Avar v_n
        with Not_found ->
            match exp with
            | Earg (Avar u_n) ->
                let rep = Env.add v_n EnCours rep
                in let rep, u_r = find_aux rep u_n
                in Env.add v_n (Replaced u_r) rep, u_r
            | Earg (Aconst _ as c) ->
                    Env.add v_n (Replaced c) rep, c
            | Ereg u_n ->
                begin let rep = Env.add v_n EnCours rep
                in let rep, u_r = find_aux rep u_n
                in match u_r with
                    | Avar _ -> Env.add v_n Keep rep, Avar v_n
                    | Aconst _ as c -> Env.add v_n (Replaced c) rep, c
                end
            | _ -> Env.add v_n Keep rep, Avar v_n
    in let rep = List.fold_left (fun rep eq -> fst (find_rep rep eq))
                    Env.empty prg.p_eqs
    in let rep = List.fold_left (fun rep out -> Env.add out Keep rep)
                    rep prg.p_outputs
    in let keep_v v_n =
        try match Env.find v_n rep with
            | Replaced u -> false | Keep -> true | _ -> assert false
        with Not_found -> true
    in let repl_v v_n =
        try match Env.find v_n rep with
            | Replaced u -> u | Keep -> Avar v_n | _ -> assert false
        with Not_found -> Avar v_n
    in let repl = function
        | Avar v -> repl_v v
        | Aconst c -> Aconst c
    in let fold_eq rt (v_n, exp) =
        match Env.find v_n rep with
        | EnCours -> assert false
        | Replaced _ -> rt
        | Keep -> (v_n, 
        match exp with 
        | Earg a -> Earg (repl a)
        | Ereg v -> begin match repl_v v with
                    | Avar u_n ->Ereg u_n
                    | Aconst _ as c -> Earg c
                    end
        | Enot a -> Enot (repl a)
        | Ebinop (b,a1,a2) -> Ebinop (b,repl a1,repl a2)
        | Emux (a1,a2,a3) -> Emux (repl a1,repl a2,repl a3)
        | Erom (i,j,a) -> Erom (i,j,repl a)
        | Eram (i,j,a1,a2,a3,a4) 
            -> Eram (i,j,repl a1,repl a2,repl a3,repl a4)
        | Econcat (a1,a2) -> Econcat (repl a1,repl a2)
        | Eslice (i,j,a) -> Eslice (i,j,repl a)
        | Eselect (i,a) -> Eselect (i,repl a)
        )::rt
    in {
        p_eqs = List.rev (List.fold_left fold_eq [] prg.p_eqs);
        p_inputs = prg.p_inputs;
        p_outputs = prg.p_outputs;
        p_vars = Env.filter (fun v_n _ -> keep_v v_n) prg.p_vars
    }

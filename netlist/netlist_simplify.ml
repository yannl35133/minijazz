open Netlist_ast

type prec_value =
    | PConst    of value
    (* v -> u,(w,i,j) si v = u = w[i:j] *)
    | PSub      of ident * (ident * int * int)

let size_of = function
    | TBit -> 1
    | TBitArray n -> n

let array_of = function
    |VBitArray a -> a
    |VBit b -> [|b|]

let slice_val s e c = Array.sub (array_of c) s (e+1-s)


let simplify : program -> program
= fun prg ->
    let eq_ev = Env.of_list prg.p_eqs in
    
    let add e k v = e := Env.add k v !e in
    let app u v = u := v :: !u          in

    (* Phase 1 : précalcul des valeurs*) 
    let def_pv v_n = 
        let sz = size_of (Env.find v_n prg.p_vars)
        in PSub (v_n, (v_n,0,sz)) in
    
    let pv = ref (List.fold_left
        (fun e v_n -> Env.add v_n (def_pv v_n) e) 
        Env.empty prg.p_inputs)   in
    let new_exp  =  ref Env.empty in
    let dfs_tg   =  ref Env.empty in

    let rec prcv v_n =
        begin try Env.find v_n !pv 
        with Not_found ->
            if Env.mem v_n !dfs_tg
            then def_pv v_n
            else begin
                add dfs_tg v_n ();
                let dep = ref [] in
                let m_exp, m_pv 
                    = do_prcv v_n dep (Env.find v_n eq_ev) in
                add pv v_n m_pv;
                add new_exp v_n (m_exp, !dep);
                m_pv
            end
        end
    and do_prcv v_n dep =
        let dpv = def_pv v_n in
        let gcst c = Earg (Aconst c), PConst c in
        let isc a ifc ifv = match a with
            | Aconst c -> ifc c
            | Avar u_n -> match prcv u_n with
            | PConst c -> ifc c
            | PSub (u_n, w) -> ifv (u_n, w)
        in let extr a =
            isc a
            (fun c -> Aconst c)
            (fun (u_n,_) -> app dep u_n; Avar u_n)
    in function
    | Earg a ->
        isc a gcst
        (fun (u_n,w) -> app dep u_n; Earg (Avar u_n), PSub (u_n,w))
    | Ereg u_n ->
        begin match prcv u_n with
        | PConst c -> gcst c
        | PSub (u_n,_) -> app dep u_n; Ereg u_n, dpv
        end
    | Enot a -> Enot (extr a), dpv
    | Ebinop (o, a0, a1) -> Ebinop (o, extr a0, extr a1), dpv
    | Emux (a0, a1, a2) -> Emux (extr a0, extr a1, extr a2), dpv
    | Erom (i,j,a) -> Erom (i,j, extr a), dpv
    | Eram (i,j,ra,we,wa,wd) ->
            Eram (i,j, extr ra, extr we, extr wa, extr wd), dpv
    | Econcat (a0, a1) -> Econcat (extr a0, extr a1), dpv
    | Eslice (s, e, a) ->
        let cst c = gcst (VBitArray (slice_val s e c))
        in isc a cst
        begin fun (_, (w_n, s', _)) ->
            app dep w_n;
            Eslice (s'+s, s'+e, Avar w_n),
            PSub (v_n, (w_n, s'+s, s'+e))
        end
    | Eselect (i, a) ->
        let cst c = gcst (VBit (array_of c).(i))
        in isc a cst
        begin fun (_, (w_n, s', _)) ->
            app dep w_n;
            Eselect (s'+i, Avar w_n),
            PSub (v_n, (w_n, s'+i, s'+i))
        end
    
    in 
    List.iter (fun v_n -> let _ = prcv v_n in ()) prg.p_outputs;

    (* Phase 2 : sélection des variables utiles *)
    let keep = List.fold_left 
        (fun e v_n -> Env.add v_n (Ereg ""(*non utilisé*)) e)
        Env.empty prg.p_inputs

    in let rec flood_fill kp v_n =
        if Env.mem v_n kp then kp
        else let exp, dep = Env.find v_n !new_exp in
            let kp = Env.add v_n exp kp in
            List.fold_left flood_fill kp dep

    in let keep = List.fold_left flood_fill keep prg.p_outputs
    in let fold_eq rt (v_n, _) =
        try (v_n, Env.find v_n keep)::rt
        with Not_found -> rt
    in let keep_vty v_n _ = Env.mem v_n keep

    in {
        p_eqs = List.rev (List.fold_left fold_eq [] prg.p_eqs);
        p_inputs = prg.p_inputs;
        p_outputs = prg.p_outputs;
        p_vars = Env.filter keep_vty prg.p_vars
    }

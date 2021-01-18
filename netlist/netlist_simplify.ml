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

let args_of = function
    | Earg a | Enot a | Erom (_,_,_,a)
    | Eslice (_,_,a) | Eselect (_, a)
        -> [a]
    | Ereg v -> [Avar v]
    | Ebinop (_,a0,a1) | Econcat (a0,a1)
        -> [a0;a1]
    | Emux (a0,a1,a2) -> [a0;a1;a2]
    | Eram (_,_,_,a0,a1,a2,a3) -> [a0;a1;a2;a3]
let deps_of exp =
    List.fold_left (fun rt -> function
        | Avar v -> v::rt
        | Aconst _ -> rt
        ) [] (args_of exp)


let simplify : program -> program
= fun prg ->

    (* Phase 1 : précalcul des valeurs *)
let prec_vals : exp Env.t -> exp Env.t
= fun eq_ev ->
    let add e k v = e := Env.add k v !e in

    let def_pv v_n =
        let sz = size_of (Env.find v_n prg.p_vars)
        in PSub (v_n, (v_n,0,sz)) in

    let pv = ref (List.fold_left
        (fun e v_n -> Env.add v_n (def_pv v_n) e)
        Env.empty prg.p_inputs)   in
    let new_exp  =  ref Env.empty in
    let dfs_tg   =  ref Env.empty in

    let isc_ p a ifc ifv = match a with
        | Aconst c -> ifc c
        | Avar u_n -> match p u_n with
        | PConst c -> ifc c
        | PSub (u_n, w) -> ifv (u_n, w)
    in let extr_ p a =
        isc_ p a
        (fun c -> Aconst c)
        (fun (u_n,_) -> Avar u_n)
    in
    (* 1a: logique combinatoire *)
    let rec prcv v_n =
        begin try Env.find v_n !pv
        with Not_found ->
            if Env.mem v_n !dfs_tg
            then raise Scheduler.Combinational_cycle
            else begin
                add dfs_tg v_n ();
                let m_exp, m_pv
                    = do_prcv v_n (Env.find v_n eq_ev) in
                add pv v_n m_pv;
                add new_exp v_n m_exp;
                m_pv
            end
        end
    and do_prcv v_n =
        let isc = isc_ prcv     in
        let extr = extr_ prcv   in
        let dpv = def_pv v_n    in
        let gcst c = Earg (Aconst c), PConst c in
    function
    | Earg a ->
        isc a gcst
        (fun (u_n,w) -> Earg (Avar u_n), PSub (u_n,w))
    | Ereg _ | Eram (_,_,_,_,_,_,_) as e
        -> e, dpv
    | Enot a -> Enot (extr a), dpv
    | Ebinop (o, a0, a1) -> Ebinop (o, extr a0, extr a1), dpv
    | Emux (a0, a1, a2) -> Emux (extr a0, extr a1, extr a2), dpv
    | Erom (i,j,f,a) -> Erom (i,j,f, extr a), dpv
    | Econcat (a0, a1) -> Econcat (extr a0, extr a1), dpv
    | Eslice (s, e, a) ->
        let cst c = gcst (VBitArray (slice_val s e c))
        in isc a cst
        begin fun (_, (w_n, s', _)) ->
            Eslice (s'+s, s'+e, Avar w_n),
            PSub (v_n, (w_n, s'+s, s'+e))
        end
    | Eselect (i, a) ->
        let cst c = gcst (VBit (array_of c).(i))
        in isc a cst
        begin fun (_, (w_n, s', _)) ->
            Eselect (s'+i, Avar w_n),
            PSub (v_n, (w_n, s'+i, s'+i))
        end
    (* 1b: logique séquentielle *)
    in let prcv_seq =
        let p v_n = Env.find v_n !pv    in
        let extr = extr_ p              in
        function
        | Ereg v_n ->
            begin match prcv v_n with
            | PConst _ -> Ereg v_n
            | PSub (u_n, _) -> Ereg u_n
            end
        | Eram (i,j,f,ra,we,wa,wd) ->
                Eram (i,j,f,extr ra,extr we,extr wa,extr wd)
        | e -> e
    in
    Env.iter (fun v_n _ -> let _ = prcv v_n in ()) eq_ev;
    Env.map prcv_seq !new_exp

    in let new_exp = prec_vals (Env.of_list prg.p_eqs) in

    (* Phase 2 : sélection des variables utiles *)
    let keep = List.fold_left
        (fun e v_n -> Env.add v_n (Ereg ""(*non utilisé*)) e)
        Env.empty prg.p_inputs

    in let rec flood_fill kp v_n =
        if Env.mem v_n kp then kp
        else let exp= Env.find v_n new_exp in
            let kp = Env.add v_n exp kp in
            List.fold_left flood_fill kp (deps_of exp)

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

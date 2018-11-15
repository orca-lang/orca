open Name
open Syntax
open Sign
open Meta
open Syntax.Int
open Print
open Print.Int
open Pp

module A = Syntax.Apx
module AP = Print.Apx

type 'a matching
  = Yes of 'a
  | Overlap
  | No

let is_match = function
  | No -> false
  | _ -> true

let is_overlap = function
  | Overlap -> true
  | _ -> false

let rec check_match cD (q : pat) (p : A.pat) =
  match q, p with
  | PVar n, A.PVar m ->
    Debug.print (fun () -> "SPLIT: Checking PVar " ^ print_name n ^ " replacing it with " ^ print_name m);
    Debug.print(fun () -> "(check_match) Sanitizing cD");
    let cD_sane = topologic_ctx cD in
    let cD' = ctx_var_subst (n, m) cD in
    Debug.print(fun () -> "(check_match) Sanitizing cD'");
    let cD'_sane = topologic_ctx cD' in
    Yes (cD', [n,PVar m])
  | PVar n, A.PClos (m, s) -> assert false
  | PVar n, _ -> Yes (cD, [])
  | PConst (n, qs), A.PConst (n', ps) when n = n' ->
    check_all cD qs ps
  | PConst (n, qs), A.PConst (n', ps) -> No
  | Inacc _, _ -> Yes (cD, [])
  | PBCtx q, _ -> bctx_check_match cD q p
  | PTBox (cP, q), p -> syn_check_match cD cP q p
  | _, A.PWildcard -> Yes (cD, [])
  | _, A.PVar n -> Overlap
  | _ -> No
and syn_check_match cD cP q p =
  match q, p with
  | PLam (xs, q), A.PLam (ys, p) ->
    syn_check_match cD (bctx_of_lam_pars cP xs) q p
  | PPar (n, pr), A.PPar (n', pr') when pr = pr'->
    Debug.print(fun () -> "(syn_check_match) Sanitizing cD");
    let cD_sane = topologic_ctx cD in
    let cD' = ctx_var_subst (n, n') cD in
    Debug.print(fun () -> "(syn_check_match) Sanitizing cD'");
    let cD'_sane = topologic_ctx cD' in
    Yes (cD', [n, PTBox (cP, PPar (n', pr))])
  | PPar (n, pr), A.PBVar (i, pr') when pr = pr' -> Yes (cD, [])
  | PUnbox (n, s), A.PClos (m, s') ->
    Debug.print (fun () -> "Punbox vs pclos: s = " ^ print_pat_subst s ^ ", s' = " ^ print_pat_subst s');
    let cP' = shift_cp_inv_pat_subst cP s' in
    let rec ctx_change = function
      | [] -> None, []
      | (n', Box(cP1, t)) :: cD' when n = n' ->
        begin match apply_inv_pat_subst (psubst_of_pat_subst s) s' with
          | None -> raise (Error.Error "Unable to apply invers substitution, go figure!")
          | Some s'' -> Some (n, m), (m, Box(cP', apply_syn_subst s'' t)) :: cD'
        end
      | (n', t) :: cD' when n = n' -> raise (Error.Violation "This shouldn't be happening. n' should have box type.")
      | (n', t) :: cD' -> let b, cD'' = ctx_change cD' in b, (n', t) :: cD''
    in
    Debug.print(fun () -> "(syn_check_match - ctx_change) Sanitizing cD");
    let cD_sane = topologic_ctx cD in
    let cD' = match ctx_change cD with
      | None, cD' -> cD'
      | Some b, cD' -> ctx_var_subst b cD'
    in
    Debug.print(fun () -> "(syn_check_match - ctx_change) Sanitizing cD'");
    let cD'_sane = topologic_ctx cD' in
    Yes (cD', [n, PTBox(cP, PUnbox (m, s'))])
  | PUnbox (n, s), A.PBVar i' ->
    begin match apply_inv_pat_subst (BVar i') s with
      | Some _ -> Yes (cD, [])
      | None -> No
    end
  | PUnbox (n, s), _ -> Yes (cD, [])
  | SInacc _, _ -> Yes (cD, [])
  | PEmpty, A.PEmpty -> Yes (cD, [])
  | PShift n, A.PShift n' when n = n' -> Yes (cD, [])
  | PBVar i, A.PBVar i' when i = i' -> Yes (cD, [])
  | PSConst (n, qs), A.PConst (n', ps) when n = n' -> syn_check_all cD cP qs ps
  | PSConst (n, ps), A.PConst (n', qs) -> No
  | PDot (s, q'), A.PDot (s', p') ->
    begin match syn_check_match cD cP s s' with
      | Yes (cD', sigma) ->
        begin match syn_check_match cD' cP (simul_syn_psubst cP sigma q') p' with
          | Yes (cD'', sigma') -> Yes (cD'', sigma' @ sigma)
          | _ -> No
        end
      | _ -> No
    end
  | _, A.PVar n -> Overlap
  | _ -> No
and bctx_check_match cD q p =
  match q, p with
  | PCtxVar x, A.PVar y  -> Yes (cD, [x, PVar y])
  | PSnoc (q1, _, q2), A.PSnoc (p1, x, p2) ->
    bctx_check_match cD q1 p1
  | PNil, A.PNil -> Yes (cD, [])
  | _ -> No
and check_all cD qs ps =
  match qs, ps with
  | q :: qs, p :: ps ->
    begin match check_match cD q p with
      | Yes (cD', s) ->
        begin match check_all cD' (simul_psubst_on_list s qs) ps with
          | Yes (cD'', s') -> Yes (cD'', s' @ s)
          | _ -> No
        end
      | _ -> No
    end
  | [], _ -> Yes (cD, [])
  | _ -> No  (* maybe we want to raise error/violation here... *)
and syn_check_all cD cP qs ps =
  match qs, ps with
  | q :: qs, p :: ps ->
    begin match syn_check_match cD cP q p with
      | Yes (cD', s) ->
        begin match syn_check_all cD' cP (simul_syn_psubst_on_list cP s qs) ps with
          | Yes (cD'', s') -> Yes (cD'', s' @ s)
          | _ -> No
        end
      | _ -> No
    end
  | [], _ -> Yes (cD, [])
  | _ -> No  (* maybe we want to raise error/violation here... *)

let is_blocking = function
  | A.PVar _
  | A.PWildcard
  | A.Inacc _
  | A.PClos _ -> false
  | _ -> true

let rec choose_blocking_var (qs : pats) (ps : A.pats) : (name * A.pat * bool) option =
  match qs, ps with
  | [], _ -> None
  | q :: qs', p :: ps' ->
    begin match choose_blocking q p with
      | Some w -> Some w
      | None -> choose_blocking_var qs' ps'
    end
  | _ -> assert false

and choose_blocking_var_syn (qs : syn_pats) (ps : A.pats) : (name * A.pat * bool) option =
  match qs, ps with
  | [], _ -> None
  | q :: qs', p :: ps' ->
    begin match choose_blocking_syn q p with
      | Some w -> Some w
      | None -> choose_blocking_var_syn qs' ps'
    end
  | _ -> assert false

(* the returned boolean expresses whether we are refining based on parameter var  *)
and choose_blocking_syn (q : syn_pat) (p : A.pat) : (name * A.pat * bool) option =
  match q, p with
  | PLam (xs, q), A.PLam(ys, p) -> 
    let rec consume_vars xs' ys' = 
      begin match xs', ys' with
        | [], [] -> choose_blocking_syn q p
        | x::xs, y::ys -> consume_vars xs ys
        | xs, [] -> choose_blocking_syn (PLam (xs, q)) p
        | _, _ -> raise (Error.Error ("Pattern has lambda abstraction " ^ AP.print_pat (A.PLam (ys, p)) ^ " with a left-hand side longer than expected."))
      end 
    in consume_vars xs ys
  | PSConst (c, qs), A.PConst(c', ps) -> choose_blocking_var_syn qs ps
  | PUnbox (n, s), p when is_blocking p -> Some (n, p, false)
  | PPar (n, _), A.PBVar i -> Some (n, p, true)
  | _ -> None

(* the returned boolean expresses whether we are refining based on parameter var  *)
and choose_blocking (q : pat) (p : A.pat) : (name * A.pat * bool) option =
  match q, p with
  | PVar n, p when is_blocking p -> Some (n, p, false)
  | PTBox(cP, q), p -> choose_blocking_syn q p
  | PConst(c, qs), A.PConst (c', ps) -> choose_blocking_var qs ps
  | _ -> None

let rec refresh_tel = function
  | (i, n, e) :: tel ->
    let n' = Name.refresh_name n in
    let sigma, tel' = refresh_tel (simul_subst_on_tel [n, Var n'] tel) in
    (n, Var n') :: sigma, (i, n', e) :: tel'
  | [] -> [], []

let split_const (sign : signature) (cD : ctx) (qs : pats)
    (n, p : name * A.pat) (c : def_name) =
  let tel_params = lookup_params sign c in
  let sigma_params, tel_params = refresh_tel tel_params in
  let params = ctx_of_tel tel_params in
  let cs = lookup_constructors sign c in
  let rec process = function
    | [] -> []
    | (c, tel, ts) :: cs' ->
      let sigma0, tel = refresh_tel (simul_subst_on_tel sigma_params tel) in
      let ts = simul_subst_on_list (sigma0 @ sigma_params) ts in
      let cD' = cD @ (ctx_of_tel tel) @ params in
      let flex = List.map fst cD' in
      (c, ts, cD', flex, (if tel == [] then Const c else App (Const c, var_list_of_tel tel)),
       PConst (c, pvar_list_of_tel tel)) :: process cs'
  in
  process cs

let split_sconst (sign : signature) (cD : ctx) (cP : bctx) (qs : pats)
    (n, p : name * A.pat) (c : def_name) =
  let cs = lookup_syn_constructors sign cP c in
  let rec process = function
    | [] -> []
    | (c, tel, ts) :: cs' ->
      let sigma0, tel = refresh_tel tel in
      let ts = simul_subst_syn_on_list sigma0 ts in
      Debug.print (fun () -> "split_sconst cD = " ^ Pretty.print_ctx cD);

      let cD' = (ctx_of_tel tel) @ cD in
      Debug.print (fun () -> "split_sconst cD' = " ^ Pretty.print_ctx cD');

      let flex = List.map fst cD' in
      (ts, cD', flex, (if tel == [] then SConst c else AppL (SConst c, unbox_list_of_tel tel)),
       PSConst (c, punbox_list_of_tel tel)) :: process cs'
  in
  let cs' = process cs in
  let rec print_processed = function
    | [] -> ""
    | (ts, cD, flex, e, e') :: cs ->
      print_syn_exp e ^ ",\n" ^
      print_processed cs
  in 
  Debug.print (fun () -> "Print processing: " ^ print_processed cs'); cs'

let split_lam (sign : signature) (cD : ctx) (cP : bctx) (qs : pats)
    (n, p : name * A.pat) (tel, t : stel * syn_exp) =
  let xs = List.map (fun (_, x, t) -> x, t) tel in
  let cP' = bctx_of_lam_pars cP xs in
  let m = Name.refresh_name n in
  let cD' = (m, Box(cP', t)) :: cD in
  let e = Unbox (Var m, id_sub) in
  let p = PUnbox (m, pid_sub) in
  [[], cD', [], Lam (xs, e), PLam (xs, p)]

type scheme_in_var
  = No
  | Yes
  | YesBlock of int * syn_exp (* which projection should the generated variable correspond to *)

let split_box (sign : signature) (cD : ctx) (qs : pats)
    (n, p : name * A.pat) (cP, t : bctx * syn_exp) =
  Debug.print (fun () -> "split_box cD = " ^ Pretty.print_ctx cD);
  Debug.print(fun () -> "Sanitizing cD");
  let cD_sane = topologic_ctx cD in
  let splits, sp = match Whnf.rewrite sign cP t with
    | SConst c -> split_sconst sign cD cP qs (n, p) c, []
    | AppL (SConst c, sp) -> split_sconst sign cD cP qs (n, p) c, sp
    | SPi (tel, t) -> Debug.print (fun () -> "split_box splitting on SPi");
      split_lam sign cD cP qs (n, p) (tel, t), []
    | SBCtx cP' -> raise Error.NotImplemented
    | SCtx _ -> raise (Error.Error "Contexts are irrelevant")
    | _ -> raise (Error.Error "Cannot split on this constructor")
  in
  let rec unify = function
    | [] -> []
    | (ts, cD', flex, e, p) :: splits ->
      Debug.print(fun () -> "Sanitizing cD'");
      let cD'_sane = topologic_ctx cD' in
      try
        Debug.print (fun () -> "splitbox preuni"); 
        let cD'', sigma = Unify.unify_flex_many_syn (sign, cD') cP flex ts sp in
        Debug.print (fun () -> "Unification: cD' = " ^ Pretty.print_ctx cD' ^ "\ncD'' = "^ Pretty.print_ctx cD''
                               ^ "\nsigma = "^ print_subst sigma);
        Debug.print(fun () -> "Sanitizing cD''");
        let cD''_sane = topologic_ctx cD'' in
        let psigma = inac_subst sigma in
        let s = n, TermBox(cP, simul_subst_syn sigma e) in
        let psigma' = (n, (PTBox (cP, simul_syn_psubst cP psigma p))) :: psigma in
        let cD''' = ctx_subst s (List.filter (fun (x, _) -> x <> n) cD'') in
        Debug.print (fun () -> "split_box1 cD''' = " ^ Pretty.print_ctx cD''');
        Some (cD''', simul_psubst_on_list psigma' qs, s :: sigma) :: unify splits
      with Unify.Unification_failure msg ->
        Debug.print_string (Unify.print_unification_problem msg);
        None :: unify splits
  in
  let rec admits_variables n = function
    | Nil -> No
    | CtxVar g ->
      begin match lookup_ctx_fail cD g with
        | Ctx (Schema ([], [_,t'])) -> (* Schema has a 1-tuple, no projections needed *)
          (* let _tel = impl_to_tel im in *)
          begin try let _ = Unify.unify_syn (sign, cD) cP t (weaken_syn (n+1) t')
              in Yes
            with Unify.Unification_failure _ -> No
          end
          
        | Ctx (Schema (quant, block)) ->
          let block', flex = mk_quant_subst cP quant block in
          let rec find n = function
            | [] -> No
            | (_, t')::block' ->
              try
                let _, sigma = Unify.unify_flex_syn (sign, cD) cP flex t t' in
                (* consider that YesBlock may only take a list of terms instead of a block *)
                (* aka: we don't want projections on arbitrary terms *)
                YesBlock (n, Block(simul_subst_in_part sigma block |> Rlist.from_list)) (* possible wrong order *)
              with Unify.Unification_failure _ -> find (n+1) block'
          in find 0 block'

        | _ -> raise (Error.Violation "Admits variable has bctx which is not a context")
      end
    | Snoc (cP', _, s) -> try let _ = Unify.unify_syn (sign, cD) cP t (weaken_syn (n+1) s) in Yes
      with Unify.Unification_failure _ -> admits_variables (n+1) cP'
  in
  match admits_variables 0 cP with
  | No -> unify splits
  | Yes ->
    let x = Name.gen_name "X" in
    Some ((x, Box (cP, t)) :: cD, simul_psubst_on_list [n, PTBox (cP, PPar (x, None))] qs, [n, Var x]) :: unify splits
  | YesBlock  (pr, Block ex) -> 
    let x = Name.gen_name "X" in
    Some ((x, Box (cP, t)) :: cD, simul_psubst_on_list [n, PTBox (cP, PPar (x, Some pr))] qs, [n, Var x]) :: unify splits

let get_splits (sign : signature) (cD : ctx) (qs : pats)
    (n, p : name * A.pat) (c, sp : def_name * exp list)
  : (ctx * pats * subst) option list =
  let splits = split_const sign cD qs (n, p) c in
  let rec unify = function
    | [] -> []
    | (c, ts, cD', flex, e, p) :: splits ->
      Debug.print (fun () -> "Unification of ts = " ^ print_exps ts
                             ^ "\nwith sp = " ^ print_exps sp
                             ^ "\nusing flex = " ^ print_names flex);
      try let cD'', sigma = Unify.unify_flex_many (sign, cD') flex ts sp in
        Debug.print (fun () -> "Resulting Unification "
                               ^ "moves context cD' = " ^ print_ctx cD'
                               ^ "\nto context " ^ print_ctx cD''
                               ^ "\nusing substitution " ^ print_subst sigma);
        let psigma = inac_subst sigma in
        let s = n, simul_subst sigma e in
        let psigma' = (n, simul_psubst psigma p) :: psigma in
        let cD''' = ctx_subst s (List.filter (fun (x, _) -> x <> n) cD'') in
        Debug.print (fun () -> "Final subst is " ^ print_subst (s :: sigma));
        Some (cD''', simul_psubst_on_list psigma' qs, s :: sigma) :: unify splits
      with Unify.Unification_failure msg ->
        Debug.print (fun () -> "Splitting on constructor " ^ c
                               ^ " resulted in unification failure\n"
                               ^ Unify.print_unification_problem msg);
        None :: unify splits
  in
  unify splits

let split_ppar (sign : signature) (cD : ctx) (qs : pats)
    (n , p : name * index) (t : exp)
  : (ctx * pats * subst) option list = assert false
(* This case will be used to split on parameter variables to produce
   corresponding cases with bound variables (to continue uncomment
   the final lines in schema.kw) *)

(* If type of pattern match function is tau, then
   tau = cG * t for some spine cG.
   cD |- sigma : cG
   . |- qs => cD

   cD' |- sigma' cD
   . |- ps => cD'
*)
let rec split (sign : signature) (cD : ctx) (qs : pats) (over : (ctx * psubst) matching)
    (ps, rhs : A.pats * A.rhs) (t : exp) : split_tree =
  Debug.print(fun () -> "Splitting qs = " ^ Pretty.print_pats cD qs
                        ^ "\nagainst ps = " ^ AP.print_pats ps
                        ^ "\ncontext is " ^ Pretty.print_ctx cD);
  match choose_blocking_var qs ps with
  | None ->
    (* Checking if we are done with patterns or if we could introduce
       more patterns to qs *)
    if List.length qs < List.length ps then
      match Whnf.whnf sign t with
      | Pi((i, n, t0) :: tel, t1) ->
        let t' = if tel = [] then t1 else Pi (tel, t1) in
        split sign ((n, t0) :: cD) (qs @ [PVar n]) over (ps, rhs) t'
      | _ -> assert false
    else
      let _ = Debug.print (fun () -> "Found leaf for " ^ AP.print_pats ps) in
      if is_overlap over then
        raise (Error.Error "Overlapping patterns not implemented yet.")
      else
        let s = rename_all qs ps in
        let qs' = simul_psubst_on_list (psubst_of_names s) qs in
        let sigma' = subst_of_names s in
        let rec subst_name n = function
          | (n', m) :: sigma when n = n' -> m
          | _ :: sigma -> subst_name n sigma
          | [] -> n                         (* name stays the same *)
        in
        let rec subst_ctx = function
          | (n, e) :: cD -> (subst_name n s, simul_subst sigma' e) :: subst_ctx cD
          | [] -> []
        in
        let cD' = subst_ctx cD in
        Debug.print (fun () -> "Renaming of qs = " ^ print_pats qs ^ "\nwith ps = " ^ AP.print_pats ps
                               ^ "\nresults in substitution " ^ print_subst sigma'
                               ^ "\nwhich moves context " ^ print_ctx cD ^ " to context " ^ print_ctx cD');
        (* Need to check inaccessible? *)
        Debug.indent ();
        let rhs' = match rhs with
          | A.Just e ->
            Just (Recon.check (sign, cD') e (simul_subst sigma' t))
          | A.Impossible n -> Impossible n (* Need to check if actually impossible *)
        in
        Debug.deindent ();
        Leaf (cD', qs', simul_subst sigma' t, rhs')
  | Some (n, p, refine) ->
    Debug.print (fun () -> "Found blocking variable " ^ print_name n);
    Debug.indent ();  
    let f = function
      | None -> None
      (* todo: figure out impossible branches for specific constructors *)
      | Some (cD', qs', sigma') ->
        Debug.print (fun () -> "split1 cD' = " ^ Pretty.print_ctx cD');
        let over' = check_all cD' qs' ps in
        begin match over' with
          | Yes (cD'', sigma) ->
            Debug.print (fun () -> "split1 cD'' = " ^ Pretty.print_ctx cD'' ^ "\nqs' = " ^ Pretty.print_pats cD'' (simul_psubst_on_list sigma qs'));
            Some (split sign cD'' (simul_psubst_on_list sigma qs') over' (ps, rhs)
                    (simul_subst (subst_of_psubst sigma) (simul_subst sigma' t)))
          | _ ->
            Some (Incomplete (cD', qs',  simul_subst sigma' t))
        end
    in
    let t = try List.assoc n cD
      with Not_found -> raise (Error.Violation ("Pattern " ^ print_pats qs
                                                ^ " has name not in context " ^ print_ctx cD))
    in
    let splits =
      if refine then
        let A.PBVar i = p in
        split_ppar sign cD qs (n, i) t
      else
        match Whnf.whnf sign t with
        | Box(cP, t) -> split_box sign cD qs (n, p) (cP, t)
        | Const c -> get_splits sign cD qs (n, p) (c, [])
        | App (Const c, sp) -> get_splits sign cD qs (n, p) (c, sp)
        | t -> raise (Error.Error ("Cannot match on type " ^ print_exp t))
    in
    Debug.deindent ();
    Debug.print (fun () -> "split1 cD = " ^ Pretty.print_ctx cD ^ "\n qs = "^ Pretty.print_pats cD qs);
    let tr = List.fold_right (function None -> fun l -> l | (Some tr) -> fun l -> tr :: l)
        (List.map f splits) []
    in
    if tr = [] then
      raise (Error.Error ("Split on variable " ^ print_name n ^ " resulted in no branches from " ^ print_pats qs))
    else
      Node (cD, qs, t, n, tr)

exception Backtrack

let rec navigate (sign : signature) (tr : split_tree) (ps, rhs : A.pats * A.rhs) : split_tree =
  match tr with
  | Incomplete (cD, qs, t) ->
    Debug.print (fun () -> "nav1 cD = " ^ Pretty.print_ctx cD);
    Debug.print(fun () -> "(nav) Sanitizing cD");
    let cD_sane = topologic_ctx cD in
    let over = check_all cD qs ps in
    begin match over with
      | Yes (cD', sigma) -> 
        Debug.print(fun () -> "(nav) Sanitizing cD'");
        let cD'_sane = topologic_ctx cD' in
        Debug.print (fun () -> "nav1 cD' = " ^ Pretty.print_ctx cD');
        split sign cD' (simul_psubst_on_list sigma qs) over (ps, rhs) (simul_subst (subst_of_psubst sigma) t)
      | _ -> raise Backtrack
    end
  | Node (cD, qs, t, n, tr') ->
    Debug.print (fun () -> "nav2 cD = " ^ Pretty.print_ctx cD);
    let over = check_all cD qs ps in
    begin match over with
      | Yes (cD', sigma) ->
        Debug.print (fun () -> "nav2 cD' = " ^ Pretty.print_ctx cD');
        let rec f = function
          | [] -> raise Backtrack
          | tr :: trs ->
            try navigate sign tr (ps, rhs) :: trs
            with Backtrack -> tr :: f trs
        in Node (cD', simul_psubst_on_list sigma qs, simul_subst (subst_of_psubst sigma) t, n, f tr')
      | _ -> raise Backtrack
    end
  | Leaf (cD, qs, _, _) ->
    begin match check_all cD qs ps with
      | Yes _ ->
        raise (Error.Error ("Branch " ^ AP.print_pats ps ^ " cannot be reached."))
      | _ ->
        raise Backtrack
    end

let check_clauses (sign : signature) (f : def_name) (t : exp) (ds : A.pat_decls) : signature_entry * split_tree =
  Debug.print (fun () -> "Starting clause checking for " ^ f);
  Debug.indent ();
  (* we add a non-reducing version of f to the signature *)
  let sign' =  (PSplit (f, t, None)) :: sign in
  let nav tr (ps, rhs) =
    Debug.print (fun () -> "Navigating through patterns " ^ AP.print_pats ps
                           ^ "\nusing tree " ^ print_tree tr);
    try navigate sign' tr (ps, rhs)
    with Backtrack ->
      raise (Error.Error ("Branch: " ^ AP.print_pats ps
                          ^ "\nwas incompatible with current tree\n" ^ Pretty.print_tree tr
                          ^ "\nTry a different split by changing the inaccessible patterns."))
  in
  let tree = List.fold_left nav (Incomplete ([], [], t)) ds in
  Debug.print (fun () -> "Generated split tree for " ^ f ^ ":\n" ^ print_tree tree);
  Debug.deindent ();
  PSplit (f, t, Some tree), tree

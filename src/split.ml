open Name
open Syntax
open Sign
open MetaOp
open MetaSub
open Syntax.Int
open Print
open Print.Int

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

let rec check_match (q : pat) (p : A.pat) =
  match q, p with
  | PVar n, A.PVar m -> Yes (PVar m)
  | PVar n, _ -> Yes q
  | PConst (n, qs), A.PConst (n', ps) when n = n' ->
    begin
    match check_all qs ps with
    | Yes qs' -> Yes (PConst (n, qs'))
    | No -> No
    | Overlap -> Overlap
    end
  | PConst (n, qs), A.PConst (n', ps) -> No
  | Inacc _, _ -> Yes q
  | PBCtx q, _ ->
    begin match bctx_check_match q p with
    | Yes q' -> Yes (PBCtx q')
    | No -> No
    | Overlap -> Overlap
    end
  | PTBox (cP, q), p ->
    begin match syn_check_match cP q p with
    | Yes q' -> Yes (PTBox (cP, q'))
    | No -> No
    | Overlap -> Overlap
    end
  | _, A.PWildcard -> Yes q
  | _, A.PVar n -> Overlap
  | _ -> No
and syn_check_match cP q p =
  match q, p with
  | PLam (xs, q), A.PLam (ys, p) ->
     begin match syn_check_match (bctx_of_lam_pars cP xs) q p with
     | Yes q' ->
       Yes (PLam (xs, q'))
     | No -> No
     | Overlap -> Overlap
     end
  | PPar n, A.PPar n' -> Yes (PPar n')
  | PUnbox (n, CShift 0, cP'), A.PClos (m, s') ->
    let cP' = shift_cp_inv_pat_subst cP s' in
    Debug.print (fun () -> "Computed context: " ^ print_bctx cP' ^ " " ^ print_pat_subst s') ;
    Yes (PUnbox (m, s', cP'))
  | PUnbox (n, s, cP'), A.PClos (m, s') when s = s' ->
    Debug.print (fun () -> "Computed context: (=) " ^ print_bctx cP' ^ " " ^ print_pat_subst s) ;
    Yes (PUnbox (n, s, cP))
  | PUnbox _, A.PClos _ -> assert false
  | PUnbox (n, s, cP'), A.PBVar i' ->
    begin match apply_inv_pat_subst (BVar i') s with
    | Some _ -> Yes (PUnbox (n, s, cP'))
    | None -> No
    end
  | PUnbox (n, s, cP'), _ -> Yes (PUnbox (n, s, cP'))
  | SInacc _, _ -> Yes q
  | PEmpty, A.PEmpty -> Yes PEmpty
  | PShift n, A.PShift n' when n = n' -> Yes (PShift n)
  | PBVar i, A.PBVar i' when i = i' -> Yes (PBVar i)
  | PSConst (n, qs), A.PConst (n', ps) when n = n' ->
    begin match syn_check_all cP qs ps with
    | Yes qs' -> Yes (PSConst (n, qs'))
    | No -> No
    | Overlap -> Overlap
    end
  | PSConst (n, ps), A.PConst (n', qs) -> No
  | PDot (s, q'), A.PDot (s', p') ->
    begin match syn_check_match cP s s', syn_check_match cP q' p' with
    | Yes s0, Yes q0 -> Yes (PDot (s0, q0))
    | _ -> No
    end
  | _, A.PVar n -> Overlap
  | _ -> No
and bctx_check_match q p =
  match q, p with
  | PCtxVar x, A.PVar y  -> Yes (PCtxVar x)
  | PSnoc (q1, _, q2), A.PSnoc (p1, x, p2) ->
    begin match bctx_check_match q1 p1 with (*, syn_check_match (bctx_of_pat_ctx q1) q2 p2 with *)
    | Yes q1' -> Yes (PSnoc (q1', x, q2))
    | _ -> No
    end
  | PNil, A.PNil -> Yes PNil
  | _ -> No
and check_all qs ps =
  match qs, ps with
  | q :: qs, p :: ps ->
    begin match check_match q p, check_all qs ps with
    | Yes q', Yes qs' -> Yes (q' :: qs')
    | _ -> No
    end
  | [], _ -> Yes []
  | _ -> No  (* maybe we want to raise error/violation here... *)
and syn_check_all cP qs ps =
  match qs, ps with
  | q :: qs, p :: ps ->
    begin match syn_check_match cP q p, syn_check_all cP qs ps with
    | Yes q', Yes qs' -> Yes (q' :: qs')
    | _ -> No
    end
  | [], _ -> Yes []
  | _ -> No  (* maybe we want to raise error/violation here... *)

let is_blocking = function
  | A.PVar _
  | A.PWildcard
  | A.Inacc _
  | A.PClos _ -> false
  | _ -> true

let rec choose_blocking_var (qs : pats) (ps : A.pats) : (name * A.pat) option =
  match qs, ps with
  | [], _ -> None
  | q :: qs', p :: ps' ->
    begin match choose_blocking q p with
    | Some w -> Some w
    | None -> choose_blocking_var qs' ps'
    end
  | _ -> assert false

and choose_blocking_var_syn (qs : syn_pats) (ps : A.pats) : (name * A.pat) option =
  match qs, ps with
  | [], _ -> None
  | q :: qs', p :: ps' ->
    begin match choose_blocking_syn q p with
    | Some w -> Some w
    | None -> choose_blocking_var_syn qs' ps'
    end
  | _ -> assert false

and choose_blocking_syn (q : syn_pat) (p : A.pat) : (name * A.pat) option =
  match q, p with
  | PLam (xs, q), A.PLam(ys, p) -> choose_blocking_syn q p
  | PSConst (c, qs), A.PConst(c', ps) -> choose_blocking_var_syn qs ps
  | PUnbox (n, s, cP), p when is_blocking p -> Some (n, p)
  | _ -> None

and choose_blocking (q : pat) (p : A.pat) : (name * A.pat) option =
  match q, p with
  | PVar n, p when is_blocking p -> Some (n, p)
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
      let cD' = cD @ (ctx_of_tel tel) in
      let flex = List.map fst cD' in
      (ts, cD', flex, (if tel == [] then SConst c else AppL (SConst c, unbox_list_of_tel cP tel)),
       PSConst (c, punbox_list_of_tel cP tel)) :: process cs'
  in
  process cs

let split_lam (sign : signature) (cD : ctx) (cP : bctx) (qs : pats)
    (n, p : name * A.pat) (tel, t : stel * syn_exp) =
  let xs = List.map (fun (_, x, t) -> x, t) tel in
  let cP' = bctx_of_lam_pars cP xs in
  let m = Name.refresh_name n in
  let cD' = (m, Box(cP', t)) :: cD in
  let e = Unbox (Var m, id_sub, cP') in
  let p = PUnbox (m, pid_sub, cP') in
  [[], cD', [], Lam (xs, e), PLam (xs, p)]

type scheme_in_var
  = No
  | Yes
  | YesBlock of int * syn_exp

let split_box (sign : signature) (cD : ctx) (qs : pats)
    (n, p : name * A.pat) (cP, t : bctx * syn_exp) =
  let splits, sp = match Whnf.rewrite sign cP t with
    | SConst c -> split_sconst sign cD cP qs (n, p) c, []
    | AppL (SConst c, sp) -> split_sconst sign cD cP qs (n, p) c, sp
    | SPi (tel, t) -> split_lam sign cD cP qs (n, p) (tel, t), []
    | SBCtx cP' -> raise Error.NotImplemented
    | SCtx _ -> raise (Error.Error "Contexts are irrelevant")
    | _ -> raise (Error.Error "Cannot split on this constructor")
  in
  let rec unify = function
    | [] -> []
    | (ts, cD', flex, e, p) :: splits ->
      try let cD'', sigma = Unify.unify_flex_many_syn (sign, cD') cP flex ts sp in
          Debug.print(fun () -> "Unification: cD' = " ^ print_ctx cD' ^ "\ncD'' = "^ print_ctx cD''
            ^ "\nsigma = "^ print_subst sigma);
          let psigma = inac_subst sigma in
          let s = n, TermBox(cP, simul_subst_syn sigma e) in
          let psigma' = (n, (PTBox (cP, simul_syn_psubst sign cP psigma p))) :: psigma in
          let cD''' = ctx_subst s (List.filter (fun (x, _) -> x <> n) cD'') in
          Some (cD''', simul_psubst_on_list sign psigma' qs, s :: sigma) :: unify splits
      with Unify.Unification_failure msg ->
        Debug.print_string (Unify.print_unification_problem msg);
        None :: unify splits
  in
  let rec admits_variables n = function
    | Nil -> No
    | CtxVar g ->
      begin match lookup_ctx_fail cD g with
        | Ctx (Schema (im, [_,t'])) -> (* Schema has a 1-tuple, no projections needed *)
          (* let _tel = impl_to_tel im in *)
          begin try let _ = Unify.unify_syn (sign, cD) cP t (Clos (t', Shift (n+1), CtxVar g))
                    in Yes
                with Unify.Unification_failure _ -> No
          end
        | Ctx (Schema (im, ex)) ->
                      let tel = impl_to_tel im in
                      let flex = List.map (fun (_, x, _) -> x) tel in
                      let rec find n = function
                        | [] -> No
                        | (_, t')::ex' ->
                           try
                             let _, sigma = Unify.unify_flex_syn (sign, cD) cP flex t t' in
                             YesBlock (n, Block(simul_subst_in_expl sigma ex |> Rlist.from_list)) (* possible wrong order *)
                           with Unify.Unification_failure _ -> find (n+1) ex'
                      in find 0 ex

                   | _ -> raise (Error.Violation "Admits variable has bctx which is not a context")
       end
    | Snoc (cP', _, s) -> try let _ = Unify.unify_syn (sign, cD) cP t (Clos (s, Shift (n+1), cP')) in Yes
                          with Unify.Unification_failure _ -> admits_variables (n+1) cP'
  in
  match admits_variables 0 cP with
  | No -> unify splits
  | Yes ->
     let x = Name.gen_name "X" in
     Some ((x, Box (cP, t)) :: cD, simul_psubst_on_list sign [n, PTBox (cP, PPar x)] qs, [n, Var x]) :: unify splits
  | YesBlock  _ -> assert false

let get_splits (sign : signature) (cD : ctx) (qs : pats)
    (n, p : name * A.pat) (c, sp : def_name * exp list) : (ctx * pats * subst) option list =
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
          let psigma' = (n, simul_psubst sign psigma p) :: psigma in
          let cD''' = ctx_subst s (List.filter (fun (x, _) -> x <> n) cD'') in
          Debug.print (fun () -> "Final subst is " ^ print_subst (s :: sigma));
          Some (cD''', simul_psubst_on_list sign psigma' qs, s :: sigma) :: unify splits
      with Unify.Unification_failure msg ->
        Debug.print (fun () -> "Splitting on constructor " ^ c
          ^ " resulted in unification failure\n"
          ^ Unify.print_unification_problem msg);
        None :: unify splits
  in
  unify splits

(* If type of pattern match function is tau, then
   tau = cG * t for some spine cG.
   cD |- sigma : cG
   . |- qs => cD

   cD' |- sigma' cD
   . |- ps => cD'
 *)
let rec split (sign : signature) (cD : ctx) (qs : pats) (over : pats matching)
    (ps, rhs : A.pats * A.rhs) (t : exp) : split_tree =
  Debug.print(fun () -> "Splitting qs = " ^ print_pats qs
    ^ "\nagainst ps = " ^ AP.print_pats ps
    ^ "\ncontext is " ^ print_ctx cD);
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
        let qs' = simul_psubst_on_list sign (psubst_of_names s) qs in
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
  | Some (n, p) ->
    Debug.print (fun () -> "Found blocking variable " ^ print_name n);
    let f = function
      | None -> None
      (* todo: figure out impossible branches for specific constructors *)
      | Some (cD', qs', sigma') ->
         let over' = check_all qs' ps in
        if is_match over' then
          Some (split sign cD' qs' over' (ps, rhs) (simul_subst sigma' t))
        else
          Some (Incomplete (cD', qs',  simul_subst sigma' t))
    in
    Debug.indent ();
    let t = try List.assoc n cD
      with Not_found -> raise (Error.Violation ("Pattern " ^ print_pats qs
        ^ " has name not in context " ^ print_ctx cD))
    in
    let splits = match Whnf.whnf sign t with
      | Box(cP, t) -> split_box sign cD qs (n, p) (cP, t)
      | Const c -> get_splits sign cD qs (n, p) (c, [])
      | App (Const c, sp) -> get_splits sign cD qs (n, p) (c, sp)
      | t -> raise (Error.Error ("Cannot match on type " ^ print_exp t))
    in
    Debug.deindent ();
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
    let over = check_all qs ps in
    begin match over with
    | Yes qs' -> split sign cD qs' over (ps, rhs) t
    | _ -> raise Backtrack
    end
  | Node (cD, qs, t, n, tr') ->
    let over = check_all qs ps in
    begin match over with
    | Yes qs' ->
      let rec f = function
        | [] -> raise Backtrack
        | tr :: trs ->
          try navigate sign tr (ps, rhs) :: trs
          with Backtrack -> tr :: f trs
      in Node (cD, qs', t, n, f tr')
    | _ -> raise Backtrack
    end
  | Leaf (cD, qs, _, _) ->
    begin match check_all qs ps with
    | Yes qs' ->
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

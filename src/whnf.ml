open Syntax
open Syntax.Int
open Print.Int
open Meta
open MetaSub
open Sign
open Util

exception Matching_failure of pat * exp
exception Matching_syn_failure of syn_pat * syn_exp
exception Stuck

let cong_stel tel s cP =
  let rec ninja tel i cP' =
    match tel with
    | [] -> [], i, cP'
    | (icit, x, e)::tel ->
       let tel', i', cP'' = ninja tel (i+1) (Snoc(cP', x, e)) in
       let s' = if i > 0 then ShiftS (i, s) else s in
       (icit, x, Clos(e, s', cP')) :: tel', i', cP''
  in
  let tel', i, cP' = ninja tel 0 cP in
  tel', (ShiftS (i, s)), cP'

let check_stuck = function (* MMMMM *)
  | Var _ -> true
  | _ -> false

let rec check_syn_stuck = function (* MMMMM *)
  | AppL(e, _)
  | Clos(e, _, _) -> true (* check_stuck e *)
  | _ -> false

let rec match_pat sign p e =
  let e = whnf sign e in
  Debug.print ~verbose:true  (fun () -> "Matching pattern " ^ print_pat p ^ " against term " ^ print_exp e);
  match p, e with
  | Inacc _, _ -> []
  | PVar n, e -> [n, e]
  | PConst (n, []), Const n' when n = n' -> []
  | PConst (n, ps), App(Const n', sp) when n = n' ->
     match_pats sign ps sp
  | PConst (n, _), App(Const n', _) ->
     raise (Matching_failure (p, e))
  | _ when check_stuck e -> raise Stuck
  | _ -> raise (Matching_failure (p, e))

and match_pats sign ps es =
  List.concat (List.map2 (match_pat sign) ps es)

and match_syn_pat sign cP p e =
  match p, rewrite sign cP e with
  | PBVar i, BVar i' when i = i' -> []
  | PLam (_, p), Lam (xs, e) -> match_syn_pat sign (bctx_from_lam cP xs) p e
  | PSConst (n, []), SConst n' when n = n' -> []
  | PSConst (n, ps), AppL(SConst n', sp) when n = n' ->
     match_syn_pats sign cP ps sp
  | PSConst (n, _), AppL(SConst n', _) ->
     raise (Matching_syn_failure (p, e))

  (* | PPar n, BVar i -> [n, BVar i] *)
  | _ when check_syn_stuck e -> raise Stuck
  | _ -> raise (Matching_syn_failure (p, e))

(* | PAnnot (p, e) -> *)
(* | PClos (n, p) -> *)
(* | PEmptyS -> *)
(* | PShift i -> *)
(* | PSubst (p1, p2) -> *)
(* | PNil -> *)
(* | PComma (p1, p2) -> *)
(* | PUnder -> *)
(* | PWildcard -> *)

and match_syn_pats sign cP ps es =
  List.concat (List.map2 (match_syn_pat sign cP) ps es)

and reduce_with_clause sign sp (pats, rhs) =
  Debug.print ~verbose:true  (fun () -> "Matching spine " ^ print_exps sp ^ " against patterns " ^ print_pats pats);
  begin try
      let sigma = match_pats sign pats sp in
      match rhs with
      | Just e -> Some (simul_subst sigma e) (* TODO this should call whnf *)
      | Impossible _ -> raise (Error.Violation "This case is impossible, it did not happen!")
    with
      Matching_failure (p, e) ->
      Debug.print ~verbose:true  (fun () -> "Term " ^ print_exp e ^ " failed to match against pattern " ^ print_pat p);
      None
  end

and reduce_with_clauses sign sp cls =
  let rec reduce sp =
    function
    | [] -> None
    | cl::cls ->
       begin match reduce_with_clause sign sp cl with
       | None -> reduce sp cls
       | otw -> otw
       end
  in
  let cl_l = List.length (fst (List.hd cls)) in
  if List.length sp < cl_l then
    None
  else
    let sp1, sp2 = split_first cl_l sp in
    try
      match reduce (List.map (whnf sign) sp1) cls with
      | None -> raise (Error.Error ("Coverage error")) (* Maybe we don't want to fail here, and just be stuck *)
      | Some e -> Some (e, sp2)
    with Stuck -> None


and whnf (sign : signature) (e : exp) : exp =
  (* Debug.print ~verbose:true  (fun () -> "Computing the whnf of " ^ print_exp e) ; *)
  Debug.indent();
  let res = match e with
    (* this removes degenerate applications should they occur *)
    | App(App(h, sp), sp') ->
       whnf sign (App(h, sp @ sp'))
    | App(h, []) ->
       whnf sign h
    | Pi (tel, Pi (tel', t)) -> whnf sign (Pi (tel @ tel', t))

    | Const n ->
      Debug.print ~verbose:true  (fun () -> "Found constant : " ^ n);
       begin match lookup_sign_def sign n with
       | D e -> Debug.print ~verbose:true  (fun () -> "Definition of " ^ n ^ " is " ^ print_exp e); whnf sign e
       | _ -> Const n
       end
    | App(h, sp) ->
      Debug.print ~verbose:true  (fun () -> "Found application. Head is: " ^ print_exp h);
      begin match whnf sign h with
      | Fn(xs, e) as f ->
        Debug.print ~verbose:true  (fun () -> "Head of application was a function " ^ print_exp f);
        let sigma = List.map2 (fun x e -> x, e) xs sp in
        whnf sign (simul_subst sigma e) (* Beta reduction *)
      | Const n ->
        Debug.print ~verbose:true  (fun () -> "Head of application was a constant " ^ print_exp (Const n));
        begin match lookup_sign_def sign n with
        | D e -> whnf sign (App (e, sp))
        | P cls ->
          begin match reduce_with_clauses sign sp cls with
          | None -> App (Const n, sp)
          | Some (e, []) -> whnf sign e
          | Some (e, sp) -> whnf sign (App (e, sp))
          end
        | _ -> App(Const n, sp)
        end
      | h -> App(h, sp)
       end
    | Annot(e, _) -> whnf sign e

    | Box (cP, e) -> Box (cP, rewrite sign cP e)
    | TermBox (cP, e) -> TermBox (cP, rewrite sign cP e)
    | e -> e
  in
  Debug.deindent();
  (* Debug.print ~verbose:true  (fun () -> "====> " ^ print_exp res); *)
  res

and rewrite (sign : signature) cP (e : syn_exp) : syn_exp =
  let w e = rewrite sign cP e in
  let dmsg msg e' =
    Debug.print ~verbose:true (fun () -> "Rewriting rule: " ^ msg);
    Debug.print ~verbose:true (fun () -> "\ne = " ^ Pretty.print_syn_exp [] cP e ^ "\ne' = " ^ Pretty.print_syn_exp [] cP (e' ()));
    e' ()
  in
  (* Debug.print ~verbose:true  (fun () -> "Rewriting " ^ print_syn_exp e); *)
  Debug.indent ();
  let res = match e with

    | AppL(AppL(h, sp), sp') -> w (AppL(h, sp @ sp'))
    | AppL(h, []) -> w h
    | SPi (tel, SPi (tel', t)) -> w (SPi (tel @ tel', t))

    | Unbox(e, s, cP') ->
       begin match whnf sign e with
       | TermBox (cP, e) -> w (Clos(e, s, cP)) (* MMMMM what about cP = cP' condition? *)
       | e -> Unbox (e, s, cP')
       end

    (* | Unbox(TermBox(cP, e), s, cP') -> raise (Error.Violation ("Okay they don't always match. Good to know\n cP = " *)
    (*                                                            ^ print_bctx cP ^ "\n cP' = " ^ print_bctx cP')) *)
    (* | Unbox(Box(cP, e), s, cP') when cP = cP' -> w (Clos(e, s, cP')) *)
    (* | Unbox(Box(cP, e), s, cP') -> raise (Error.Violation ("Okay they don't always match. Good to know\n cP = " *)
    (*                                                            ^ print_bctx cP ^ "\n cP' = " ^ print_bctx cP')) *)


  (* Syntactic rewriting rules *)

  (* Beta reduction *)
    | AppL(e, es) ->
      begin match w e with
      | Lam (xs, e1) ->
        let rec f es = match es with
          | [] -> Shift 0
          | e :: es -> Dot (f es, e)
        in
        w (dmsg "beta reduction" (fun () -> (Clos(e1, f es, bctx_from_lam cP xs))))
      | e -> AppL(e, es)
      end

  (* IdL *)
  | Comp(Shift 0, _, s) -> w (dmsg "IdL" (fun () -> s))

  (* IdR *)
  | Comp(s, _, Shift 0) -> w (dmsg "IdR" (fun () -> s))

  (* LiftId *)
  | ShiftS(n, Shift 0) -> (dmsg "LiftId" (fun () -> (Shift 0)))

  (* Id *)
  | Clos (e, Shift 0, _) -> w (dmsg "Id" (fun () -> e))

  (* Empty Subst *)
  | Clos (e, Empty, _) -> w (dmsg "Empty" (fun () -> e))

  (* VarShift 1 *)
  | Clos(BVar n, Shift n', _) -> (dmsg "VarShift 1" (fun () -> (BVar (n + n'))))

  (* VarShift 2 *)
  | Clos(BVar n, Comp(s, cP, Shift n'), _) -> w (dmsg "VarShift 2" (fun () -> (Clos(BVar (n + n'), s, cP))))

  (* FVarsCons *)
  | Clos(BVar 0, Dot (s, e), _) -> w (dmsg "FVarsCons" (fun () -> e))

  (* FVarLift 1 *)
  | Clos(BVar i, ShiftS (n, s), _) when i < n -> (dmsg "FVarLift 1" (fun () -> (BVar i)))

  (* FVarLift 2 *)
  | Clos(BVar i, Comp(s2, cP, ShiftS (n, s1)), _) when i < n -> w (dmsg "FVarLift 2" (fun () -> (Clos(BVar i, s2, cP))))

  (* RVarCons *)
  | Clos (BVar n, Dot(s, _), Snoc (cP, _, _)) when n > 0 -> w (dmsg "RVarCons" (fun () -> (Clos(BVar (n-1), s, cP))))

  (* RVarLift 1 *)
  | Clos (BVar n, ShiftS (m, s), cP) when n >= m ->
     w (dmsg "RVarLift 1" (fun () -> (Clos(BVar (n-m), Comp(Shift m, keep_suffix cP m, s), drop_suffix cP m))))

  (* RVarLift 2 *)
  | Clos (BVar n, Comp(s2, cP1, ShiftS (m, s1)), cP) when n >= m ->
     w (dmsg "RVarLift 2" (fun () -> (Clos(BVar (n-m), Comp (Comp(s2, cP1, Shift m), drop_suffix cP1 m, s1), drop_suffix cP m))))

  (* AssEnv *)
  | Comp(s1, cP1, Comp(s2, cP2, s3)) -> w (dmsg "AssEnv" (fun () -> (Comp(Comp(s1, cP1, s2), cP2, s3))))

  (* MapEnv *)
  | Comp(s2, cP, Dot(s1, e)) -> w (dmsg "MapEnv" (fun () -> (Dot(Comp(s2, cP, s1), Clos(e, s2, cP)))))

  (* ShiftCons *)
  | Comp(Dot(s, e), Snoc (cP, _, _), Shift n) -> w (dmsg "ShiftCons" (fun () -> (Comp(s, cP, Shift (n-1)))))

  (* ShiftLift 1 *)
  | Comp(ShiftS (m, s), cP, Shift n) when m < n ->
     w (dmsg "ShiftLift 1a" (fun () -> (Comp (Comp(Shift m, assert false, s), drop_suffix cP m, Shift (n-m)))))
  | Comp(ShiftS (m, s), cP, Shift n) when m = n -> w (dmsg "ShiftLift 1b" (fun () -> (Comp(Shift n, assert false, s))))
  | Comp(ShiftS (m, s), cP, Shift n) -> w (dmsg "ShiftLift 1c" (fun () -> (Comp(Shift n, assert false, ShiftS (m-n, s)))))

  (* ShiftLift 2 *)
  | Comp(Comp(s2, cP1, ShiftS (m, s)), cP2, Shift n) when n > m ->
     w (dmsg "ShiftLift 2a" (fun () -> (Comp(Comp(Comp(s2, cP1, Shift m), drop_suffix cP1 m, s), drop_suffix cP2 m, Shift (n-m)))))
  | Comp(Comp(s2, cP1, ShiftS (m, s)), cP2, Shift n) when n = m ->
     w (dmsg "ShiftLift 2b" (fun () -> (Comp(Comp(s2, cP1, Shift m), drop_suffix cP1 m, s))))
  | Comp(Comp(s2, cP1, ShiftS (m, s)), cP2, Shift n) -> assert false
  (*    w (dmsg "ShiftLift 2c" (Comp(Comp(Comp(s2, cP1, Shift m), drop_suffix cP1 m, s), drop_suffix cP2 m, Shift (n-m)))) *)

  (* Lift 1 *)
  | Comp(ShiftS (n, s1), cP, ShiftS (m, s2)) when n = m -> w (dmsg "Lift 1" (fun () -> (ShiftS (n, Comp (s1, drop_suffix cP m, s2)))))
  | Comp(ShiftS (n, s1), cP, ShiftS (m, s2)) when n < m ->
     w (dmsg "Lift 1" (fun () -> (ShiftS (n, Comp (s1, drop_suffix cP n, ShiftS (m-n, s2))))))
  | Comp(ShiftS (n, s1), cP, ShiftS (m, s2)) ->
     w (dmsg "Lift 1" (fun () -> (ShiftS (m, Comp (ShiftS (n-m, s1), drop_suffix cP m, s2)))))

  (* Lift 2 *)
  | Comp(Comp (s1, cP1, ShiftS (n, s2)), cP2, ShiftS (m, s3)) when n = m ->
     w (dmsg "Lift 2" (fun () -> (Comp (s1, cP1, ShiftS(n, Comp (s2, drop_suffix cP2 n, s3))))))
  | Comp(Comp (s1, cP1, ShiftS (n, s2)), cP2, ShiftS (m, s3)) when n < m ->
     w (dmsg "Lift 2" (fun () -> (Comp (s1, cP1, ShiftS(n, Comp (s2, drop_suffix cP2 n, ShiftS (m-n, s3)))))))
  | Comp(Comp (s1, cP1, ShiftS (n, s2)), cP2, ShiftS (m, s3)) ->
     w (dmsg "Lift 2" (fun () -> (Comp (s1, cP1, ShiftS(m, Comp (ShiftS (n-m, s2), drop_suffix cP2 m, s3))))))


  (* LiftEnv *)
  | Comp(Dot(s2,e), Snoc(cP, _, _) , ShiftS (n, s1)) when n > 0 ->
     w (dmsg "LiftEnv" (fun () -> (Dot(Comp(s2, cP, (ShiftS (n-1, s1))), e))))

  | Comp (Shift n, _, Shift m) -> (dmsg "ShiftAdd" (fun () -> (Shift (n+m))))

  (* Added rules for confluence *)
  | Clos (e, Comp (s, _, Empty), _) -> w (dmsg "CompEmpty" (fun () -> e))

  (* Congruence rules *)
  | Clos (SConst n, _, _) -> dmsg "CongClosConst" (fun () -> (SConst n))
  | Clos (Clos (e, s1, cP1), s2, cP2) -> w (dmsg "CongClosClos" (fun () -> (Clos (e, Comp(s2, cP2, s1), cP1))))
  | Clos (Unbox (e, s1, cP1), s2, cP2) -> w (dmsg "CongClosUnbox" (fun () -> (Unbox (e, Comp(s2, cP2, s1), cP1))))
  | Clos (AppL(e, es), s, cP) -> w (dmsg "CongClosAppL" (fun () -> (AppL(Clos(e, s, cP), List.map (fun e-> Clos(e, s, cP)) es))))
  | Clos (Lam (xs, e), s, cP) ->
     (dmsg "CongClosLam"
           (fun () -> (Lam (xs, Clos (e, fst (List.fold_left (fun (s, i) _ -> ShiftS (i+1, s), i+1) (s, 0) xs), bctx_from_lam cP xs)))))
  | Clos (Star, s, _) -> (dmsg "CongClosStar" (fun () -> Star))
  | Clos (SPi(tel, t), s, cP) ->
     let tel', s, cP' = cong_stel tel s cP in
    (dmsg "CongClosSPi" (fun () -> (SPi (tel', Clos (t, s, cP')))))

 (* Contexts bind their own variables *)
  (* | Clos (Ctx, s) -> Ctx *)
  (* | Clos (Snoc (g, x, t), s) -> Snoc (g, x, t) *)
  (* | Clos (Nil, s) -> Nil *)

  (* Not quite weak head normalisation *)
  | Clos (e, s, cP) -> let s' = w s in
                   let e' = w e in
                   if s = s' && e' = e then
                     Clos (e, s, cP)
                   else w (dmsg "DeepClosRew" (fun () -> (Clos (e', s', cP))))
  | Comp (e1, cP, e2) ->
    let e1' = w e1 in
    let e2' = w e2 in
    if e1 = e1' && e2 = e2' then
      Comp (e1, cP, e2)
    else w (dmsg "DeepCompRew" (fun () -> (Comp (e1', cP, e2'))))
  | Dot(e, s) ->
    let e' = w e in
    let s' = w s in
    if e = e' && s = s' then
      Dot (e, s)
    else w (dmsg "DeepDotRew" (fun () -> (Dot (e', s'))))

  (* IDK what to do with these *)
  (* | Clos (Box(g, t), s) -> assert false *)

(*
  (* rewriting rules here (Work in progress) *)
  | Clos (Const n, _) -> whnf sign (Const n)
  | Clos (BVar 0, Dot (_, e)) -> whnf sign e
  | Clos (BVar n, Dot (s, _)) -> whnf sign (Clos (BVar (n-1), s))
  | Clos (App (e, es), s) -> whnf sign (App (Clos (e, s), List.map (fun e -> Clos (e, s)) es))
  (* We might be missing the case for lam here *)
  | Comp (s1, (Dot (s2, e))) -> whnf sign (Dot (Comp (s1, s2), Clos (e, s1)))
  | Clos (Clos (e, s1), s2) -> whnf sign (Clos (e, Comp (s1, s2)))
  | Comp (Dot (s1, e), ShiftS s2) -> whnf sign (Dot (Comp (s1, s2), e))
  | Clos (e, Shift 0) -> whnf sign e
  | Comp (Shift 0, s) -> whnf sign s
  | Comp (s, Shift 0) -> whnf sign s
  | Comp (ShiftS s, Shift n) -> whnf sign (Comp (Comp (Shift 1, s), Shift (n-1)))
  | Comp (Comp (s1, ShiftS s2), Shift n) -> whnf sign (Comp (Comp (Comp (s1, Shift 1), s2), Shift (n-1)))
  | Clos (BVar i, Shift n) -> BVar (i+n)
  | Clos (BVar 0, ShiftS _) -> BVar 0
  | Clos (BVar n, ShiftS s) -> whnf sign (Clos (BVar (n-1), (Comp (Shift 1, s))))
  | Clos (BVar n, Comp (s1, ShiftS s2)) when n > 0 -> whnf sign (Clos (BVar (n-1), Comp (Comp (s1, Shift 1), s2)))
  | Comp (Dot (e, s), Shift n) when n>0 -> whnf sign (Comp (s, Shift (n-1)))
  | Clos (BVar i, Comp (s, Shift n)) -> whnf sign (Clos (BVar (i+n), s))
  | Comp (ShiftS s1, ShiftS s2) -> whnf sign (ShiftS (Comp (s1, s2)))
  | Comp (Comp (s1, ShiftS s2), ShiftS s3) -> whnf sign (Comp (s1, ShiftS (Comp (s2, s3))))
  | ShiftS (Shift 0) -> Shift 0
  | Clos (Lam (xs, e), s) -> Lam (xs, Clos (e, List.fold_left (fun s _ -> ShiftS s) s xs))
       *)

  | e -> e (* No reduction necessary *)

  in
  Debug.deindent ();
  (* Debug.print ~verbose:true  (fun () -> "===> " ^ print_syn_exp res); *)
  res

let rec whnf_ctx sign = function
  | [] -> []
  | (x, t) :: cG -> (x, whnf sign t) :: whnf_ctx sign cG

let rec whnf_bctx sign = function
  | Nil -> Nil
  | CtxVar g -> CtxVar g
  | Snoc (cP, x, t) ->
    let cP' = whnf_bctx sign cP in
    Snoc (cP', x, rewrite sign cP' t)

let rec whnf_stel sign cP = function
  | [] -> []
  | (i, x, t) :: tel -> (i, x, rewrite sign cP t) :: (whnf_stel sign (Snoc(cP, x, t)) tel)

let rec normalize sign (e : exp) =
  let norm e = normalize sign e in
  match whnf sign e with
  | Set n -> Set n
  | Pi (tel, t) ->
    let tel' = List.map (fun (i, x, t) -> i, x, norm t) tel in
    let t' = norm t in
    Pi (tel', t')
  | Box (cP, e) ->
    let cP' = normalize_bctx sign cP in
    Box (cP', normalize_syn sign cP e)
  | Ctx  -> Ctx
  | Const n -> Const n
  | Dest n -> Dest n
  | Var x -> Var x
  | Fn (xs, e) -> Fn (xs, norm e)
  | App (e, es) -> App(norm e, List.map norm es)
  | BCtx cP -> BCtx (normalize_bctx sign cP)
  | Annot (e, t) -> Annot (norm e, norm t)
  | Hole i -> Hole i
  | TermBox (cP, e) ->
    let cP' = normalize_bctx sign cP in
    Box (cP', normalize_syn sign cP e)

and normalize_syn sign cP e =
  let norm e = normalize_syn sign cP e in
   match rewrite sign cP e with
   | Lam (xs, t) -> Lam (xs, normalize_syn sign (bctx_from_lam cP xs) t)
   | AppL (e, es) -> AppL (norm e, List.map norm es)
   | SConst n -> SConst n
   | BVar i -> BVar i
   | Clos (e, s, cP') ->
     let cP'' = normalize_bctx sign cP' in
     Clos (normalize_syn sign cP'' e, norm s, cP'')
   | Empty -> Empty
   | Dot (s,e) -> Dot (norm s, norm e)
   | Comp (e1, cP, e2) ->
     let cP' = normalize_bctx sign cP in
     Comp(norm e1, cP', normalize_syn sign cP' e2)
   | Shift n -> Shift n
   | ShiftS (n, s) -> ShiftS (n, normalize_syn sign (drop_suffix cP n) s)
   | Star  -> Star
   | SPi (tel, t) ->
     let f (tel, cP) (i, x, t) =
       let t' = normalize_syn sign cP t in
       (tel @ [i, x, t']), Snoc(cP, x, t')
     in
     let tel', cP' = List.fold_left f ([], cP) tel in
     SPi (tel', normalize_syn sign cP' t)
   | SBCtx cP -> SBCtx (normalize_bctx sign cP)
   | SCtx  -> SCtx
   | Unbox (e,s, cP') ->
     let cP'' = normalize_bctx sign cP' in
     Unbox (normalize sign e, norm s, cP'')

and normalize_bctx sign cP =
  match cP with
  | CtxVar n -> CtxVar n
  | Nil -> Nil
  | Snoc(cP, x, t) ->
    let cP' = normalize_bctx sign cP in
    Snoc(cP', x, normalize_syn sign cP' t)

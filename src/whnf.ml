open Syntax
open Syntax.Int
open Print.Int
open Meta
open Util

exception Matching_failure of pat * exp
exception Matching_syn_failure of syn_pat * syn_exp

exception Matching_tree_failure
exception Stuck

let safe_mode = ref false

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
  | PTBox (cP, p), TermBox(cP', e) ->
     match_syn_pat sign cP' p e
  | _ -> raise (Matching_failure (p, e))

and match_pats sign ps es =
  Debug.print ~verbose:true (fun () -> "ps = " ^ print_pats ps ^ "\nes = " ^ print_exps es);
  let rec map ps es = match ps, es with
    | [], _ -> []
    | p :: ps, e :: es -> match_pat sign p e @ map ps es
    | _ -> raise Matching_tree_failure
  in
  map ps es

and match_syn_pat sign cP p e =
  match p, rewrite sign cP e with
  | PBVar i, BVar i' when i = i' -> []
  | PLam (_, p), Lam (xs, e) -> match_syn_pat sign (bctx_of_lam_pars cP xs) p e
  | PSConst (n, []), SConst n' when n = n' -> []
  | PSConst (n, ps), AppL(SConst n', sp) when n = n' ->
     match_syn_pats sign cP ps sp
  | PSConst (n, _), AppL(SConst n', _) ->
     raise (Matching_syn_failure (p, e))
  | PUnbox (n, s), e  ->
     begin match apply_inv_pat_subst e s with
     | None -> raise (Matching_syn_failure (p, e))
     | Some e' -> 
     let cP' = apply_inv_psubst_ctx cP s in
     [n, TermBox (cP', e')]
     end
  | PPar (n, pr), BVar (i, pr') when pr = pr' -> [n, TermBox (cP, BVar (i, pr'))]
  | _ -> raise (Matching_syn_failure (p, e))

(* | PAnnot (p, e) -> *)
(* | PClos (n, p) -> *)
(* | PEmpty -> *)
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
    | Matching_syn_failure (p, e) ->
      Debug.print ~verbose:true  (fun () -> "Term " ^ print_syn_exp e ^ " failed to match against pattern " ^ print_syn_pat p);
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
  if cls = [] then None
  else
    let cl_l = List.length (fst (List.hd cls)) in
    if List.length sp < cl_l then
      None
    else
      let sp1, sp2 = split_first cl_l sp in
      match reduce (List.map (whnf sign) sp1) cls with
      | None -> None
      | Some e -> Some (e, sp2)

and walk_tree (sign : signature) (sp : exp list) (tr : split_tree list) : exp =
  match tr with
  | Node(_, ps, _, _, tr) :: tr' ->
    begin try
      let _ = match_pats sign ps sp in
      walk_tree sign sp tr
    with Matching_failure _ -> walk_tree sign sp tr'
    | Matching_syn_failure _ -> walk_tree sign sp tr'
    end
  | Leaf (_, ps, _, Just e) :: tr' ->
    begin try
      let sigma = match_pats sign ps sp in
      simul_subst sigma e
    with Matching_failure _ -> walk_tree sign sp tr'
    | Matching_syn_failure _ -> walk_tree sign sp tr'
    | Matching_tree_failure -> walk_tree sign sp tr'
    end
  | Incomplete _ :: _ -> raise (Error.Violation "Found incomplete tree branch in the signature while reducing.")
  | Leaf (cD, ps, t, Impossible n) :: tr' ->
    if !safe_mode then
      begin try
              let _ = match_pats sign ps sp in
              raise (Error.Violation "Impossible leaf is matched during reduction.")
        with Matching_failure _ -> walk_tree sign sp tr'
        | Matching_syn_failure _ -> walk_tree sign sp tr'
        | Matching_tree_failure -> walk_tree sign sp tr'
      end
    else
      walk_tree sign sp tr'
  | [] -> raise Stuck

and whnf (sign : signature) (e : exp) : exp =
  (* Debug.print ~verbose:true  (fun () -> "Computing the whnf of " ^ print_exp e) ; *)
  Debug.indent();
  let res = match e with
    (* this removes degenerate applications should they occur *)
    | App(App(h, sp), sp') ->
       whnf sign (App(h, sp @ sp'))
    | App(h, []) ->
      whnf sign h
    | Pi ([], t) -> whnf sign t
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
        let rec map xs sp =
          match xs, sp with
          | [], sp -> [], [], sp
          | x::xs, e :: sp ->
            let sigma, xs', sp' = map xs sp in
            (x, whnf sign e) :: sigma, xs', sp' (* we evaluate e for call by value *)
          | xs, [] -> [], xs, sp
        in
        let sigma, xs', sp' = map xs sp in
        let e' = simul_subst sigma e in
        if xs' <> [] then
          Fn(xs', e')
        else if sp' <> [] then
          whnf sign (App (e', sp'))
        else
          whnf sign e'
      | Const n ->
        Debug.print ~verbose:true  (fun () -> "Head of application was a constant " ^ print_exp (Const n));
        begin match lookup_sign_def sign n with
        | D e -> whnf sign (App (e, sp))
        | P cls -> Debug.print ~verbose:true (fun () -> "Definition " ^ n ^ " has clause list " ^ String.concat "\n" (List.map (fun cl -> print_pats (fst cl)) cls));
          begin match reduce_with_clauses sign sp cls with
          | None -> App (Const n, sp)
          | Some (e, []) -> whnf sign e
          | Some (e, sp) -> whnf sign (App (e, sp))
          end
        | S tree ->
          Debug.print (fun () -> "Matching split tree for expression " ^ print_exp e);
          begin try whnf sign (walk_tree sign sp [tree])
            with Stuck -> App(Const n, sp)
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

    | Unbox(e, s) ->
       begin match whnf sign e with
       | TermBox (cP, e) -> w (apply_syn_subst s e)
       | e -> Unbox (e, s)
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
        w (dmsg "beta reduction" (fun () -> (apply_syn_subst (f es) e1)))
      | e -> AppL(e, es)
      end

  | Dot(e, s) -> (dmsg "DeepDotRew" (fun () -> 

    let e' = w e in
    let s' = w s in
    if e = e' && s = s' then
      Dot (e, s)
    else w (Dot (e', s'))))

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
  | Ctx sch  -> Ctx (normalize_schema sign sch)
  | Const n -> Const n
  | Var x -> Var x
  | Fn (xs, e) -> Fn (xs, norm e)
  | App (e, es) -> App(norm e, List.map norm es)
  | BCtx cP -> BCtx (normalize_bctx sign cP)
  | Annot (e, t) -> Annot (norm e, norm t)
  | Hole i -> Hole i
  | TermBox (cP, e) ->
    let cP' = normalize_bctx sign cP in
    Box (cP', normalize_syn sign cP e)

and normalize_schema sign (Schema (quant, block)) =
  Schema (quant, block)             (* TODO add normalization *)

and normalize_stel sign cP tel =
  let f (tel, cP) (i, x, t) =
    let t' = normalize_syn sign cP t in
    (tel @ [i, x, t']), Snoc(cP, x, t')
  in
  List.fold_left f ([], cP) tel


and normalize_syn sign cP e =
  let norm e = normalize_syn sign cP e in
   match rewrite sign cP e with
   | Lam (xs, t) -> Lam (xs, normalize_syn sign (bctx_of_lam_pars cP xs) t)
   | AppL (e, es) -> AppL (norm e, List.map norm es)
   | SConst n -> SConst n
   | BVar i -> BVar i
   | Empty -> Empty
   | Dot (s,e) -> Dot (norm s, norm e)
   | Shift n -> Shift n
   | Star  -> Star
   | SPi (tel, t) ->
     let tel', cP' = normalize_stel sign cP tel in
     SPi (tel', normalize_syn sign cP' t)
   | SBCtx cP -> SBCtx (normalize_bctx sign cP)
   | SCtx sch -> SCtx (normalize_schema sign sch)
   | Unbox (e,s) ->
     Unbox (normalize sign e, norm s)
   | Block cs -> Block (Rlist.map (fun (x, e) -> x, norm e) cs)
   | TBlock _ -> assert false

and normalize_bctx sign cP =
  match cP with
  | CtxVar n -> CtxVar n
  | Nil -> Nil
  | Snoc(cP, x, t) ->
    let cP' = normalize_bctx sign cP in
    Snoc(cP', x, normalize_syn sign cP' t)

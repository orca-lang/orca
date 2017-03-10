open Syntax.Int
open Sign

exception Matching_failure of pat * exp
exception Stuck

exception Inv_fail

let apply_inv e s =
  let rec add_id_cdot n s =
    if n = 0 then s
    else CDot(add_id_cdot (n-1) s, n-1)
  in
  let rec apply_inv e s =
    let rec apply_inv' n s cnt =
      match s with
      | CDot (s, m) when n = m -> BVar cnt
      | CDot (s, _) -> apply_inv' n s (cnt+1)
      | CShift m when n < m -> raise Inv_fail
      | CShift m -> BVar (n - m)
      | CEmpty -> raise Inv_fail
    in
    match e, s with
    | e, CShift 0 -> e
    | BVar n, _ -> apply_inv' n s 0
    | Set n, _ -> Set n
    | Star, _ -> Star
    | Pi(tel, t'), _ ->
      Pi(List.map (fun (i,x,e) -> i, x, apply_inv e s) tel, apply_inv t' s)
    | SPi(tel, t'),_ ->
      SPi(List.map (fun (i,x,e) -> i, x, apply_inv e s) tel, apply_inv t' (add_id_cdot (List.length tel) s))
    | Box (g, e), _ -> raise Inv_fail
    | Ctx, _ -> Ctx
    | Const c, _ -> Const c
    | Var x, _ -> Var x                 (* MMMM *)
    | Fn (xs, e),_ -> Fn (xs, apply_inv e s)
    | App (e, es),_ -> App(apply_inv e s, List.map (fun e -> apply_inv e s) es)
    | Lam (x, e), _ -> Lam(x, apply_inv e (CDot (s, 0)))
    | AppL (e, es), _ -> AppL(apply_inv e s, List.map (fun e -> apply_inv e s) es)
    | Hole n, _ -> Hole n
    | Annot (e1, e2), _ -> Annot (apply_inv e1 s, apply_inv e2 s)
    | Snoc _, _ -> e
    | Nil, _ -> Nil
      
    | Clos (e, s'), _ -> Clos(e, apply_inv s' s)
      
    | EmptyS,_ -> EmptyS
    | Shift _, _ 
      
    | Dot _, _
    | Comp _, _
    | ShiftS _, _-> assert false

  in
  try Some (apply_inv e s)
  with Inv_fail -> None
  
let rec cong_stel tel s =
  match tel with
  | [] -> [], s
  | (i, x, e)::tel ->
     let tel', s = cong_stel tel (ShiftS s) in
     (i, x, Clos(e, s)) :: tel', s

let rec match_pat sign p e =
  let e = whnf sign e in
  Debug.print (fun () -> "Matching pattern " ^ print_pat p ^ " against term " ^ print_exp e);
  match p, e with
  | Innac _, _ -> []
  | PVar n, e -> [n, e]
  | PPar n, BVar i -> [n, BVar i]
  | PBVar i, BVar i' when i = i' -> []
  | PLam (_, p), Lam (_, e) -> match_pat sign p e

  | PConst (n, []), Const n' when n = n' -> []
  | PConst (n, ps), App(Const n', sp) when n = n' ->
     match_pats sign ps sp
  | PConst (n, _), App(Const n', _) ->
     raise (Matching_failure (p, e))
  | _, Var _ -> raise Stuck
  | _ -> raise (Matching_failure (p, e))

(* | PAnnot (p, e) -> *)
(* | PClos (n, p) -> *)
(* | PEmptyS -> *)
(* | PShift i -> *)
(* | PSubst (p1, p2) -> *)
(* | PNil -> *)
(* | PComma (p1, p2) -> *)
(* | PUnder -> *)
(* | PWildcard -> *)

and match_pats sign ps es =
  List.concat (List.map2 (match_pat sign) ps es)

and reduce_with_clause sign sp (pats, rhs) =
  Debug.print (fun () -> "Matching spine " ^ print_exps sp ^ " against patterns " ^ print_pats pats);
  begin try
      let sigma = match_pats sign pats sp in
      match rhs with
      | Just e -> Some (simul_subst sigma e) (* TODO this should call whnf *)
      | Impossible _ -> raise (Error.Violation "This case is impossible, it did not happen!")
    with
      Matching_failure (p, e) ->
      Debug.print (fun () -> "Term " ^ print_exp e ^ " failed to match against pattern " ^ print_pat p);
      None
  end

and reduce_with_clauses sign sp cls =
  let rec split n sp =
    match n, sp with
    | 0, _ -> [], sp
    | _, p :: sp' ->
       let sp1, sp2 = split (n-1) sp' in
       p :: sp1, sp2
    | _ -> raise (Error.Violation "This will not happen")
  in
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
    let sp1, sp2 = split cl_l sp in
    try
      match reduce sp1 cls with
      | None -> raise (Error.Error ("Coverage error"))
      | Some e -> Some (e, sp2)
    with Stuck -> None


and whnf (sign : signature) (e : exp) : exp =
  (* Debug.print (fun () -> "Computing the whnf of " ^ print_exp e ^ ".") ; *)
  Debug.indent();
  let res = match e with
    (* this removes degenerate applications should they occur *)
    | App(App(h, sp), sp') ->
       whnf sign (App(h, sp @ sp'))
    | App(h, []) ->
       whnf sign h
    | Pi (tel, Pi (tel', t)) -> whnf sign (Pi (tel @ tel', t))
    | SPi (tel, SPi (tel', t)) -> whnf sign (SPi (tel @ tel', t))

    | Const n ->
       begin match lookup_sign_def n sign with
       | D e -> whnf sign e
       | _ -> Const n
       end
    | App(Const n, sp) ->
       begin match lookup_sign_def n sign with
       | D e -> whnf sign (App (e, sp))
       | P cls ->
          begin match reduce_with_clauses sign sp cls with
          | None -> App (Const n, sp)
          | Some (e, []) -> whnf sign e
          | Some (e, sp) -> whnf sign (App (e, sp))
          end
       | _ -> App(Const n, sp)
       end
    | App(h, sp) ->
       begin match whnf sign h with
       | Fn(xs, e) ->
          let sigma = List.map2 (fun x e -> x, e) xs sp in
          whnf sign (simul_subst sigma e) (* Beta reduction *)
       | h -> App(h, sp)
       end
    | Annot(e, _) -> whnf sign e


    | e -> rewrite sign e
  in
  Debug.deindent();
  (* Debug.print (fun () -> "Whnf of " ^ print_exp e ^ " is " ^ print_exp res ^ "."); *)
  res

and rewrite (sign : signature) (e : exp) : exp =
  let w = whnf sign in
  let res = match e with

  (* Syntactic rewriting rules *)

  (* Beta reduction *)
    | AppL(Lam (_, e1), es) ->
      let rec f es = match es with
        | [] -> Shift 0
        | e :: es -> Dot (f es, e)
      in
      w (Clos(e1, f es))
      
  (* IdL *)
  | Comp(Shift 0, s) -> w s

  (* IdR *)
  | Comp(s, Shift 0) -> w s

  (* LiftId *)
  | ShiftS(Shift 0) -> Shift 0

  (* Id *)
  | Clos (e, Shift 0) -> w e

  (* Empty Subst *)
  | Clos (e, EmptyS) -> w e
         
  (* VarShift 1 *)
  | Clos(BVar n, Shift n') -> BVar (n + n')

  (* VarShift 2 *)
  | Clos(BVar n, Comp(s, Shift n')) -> w (Clos(BVar (n + n'), s))

  (* FVarsCons *)
  | Clos(BVar 0, Dot (s, e)) -> w e

  (* FVarLift 1 *)
  | Clos(BVar 0, ShiftS s) -> BVar 0

  (* FVarLift 2 *)
  | Clos(BVar 0, Comp(s2, ShiftS s1)) -> w (Clos(BVar 0, s2))

  (* RVarCons *)
  | Clos (BVar n, Dot(s, _)) when n > 0 -> w (Clos(BVar (n-1), s))

  (* RVarLift 1 *)
  | Clos (BVar n, ShiftS s) when n > 0 -> w (Clos(BVar (n-1), Comp(Shift 1, s)))

  (* RVarLift 2 *)
  | Clos (BVar n, Comp(s2, ShiftS s1)) when n > 0 -> w (Clos(BVar (n-1), Comp (s1, Comp(Shift 1, s2))))

  (* AssEnv *)
  | Comp(s1, Comp(s2, s3)) -> w (Comp(Comp(s1, s2), s3))

  (* MapEnv *)
  | Comp(s2, Dot(s1, e)) -> w (Dot(Comp(s2, s1), Clos(e, s2)))

  (* ShiftCons *)
  | Comp(Dot(s, e), Shift n) -> w (Comp(s, Shift (n-1)))

  (* ShiftLift 1 *)
  | Comp(ShiftS s, Shift n) -> w (Comp(Shift n, s)) (* MMMM *)

  (* ShiftLift 2 *)
  | Comp(Comp(s2, ShiftS s), Shift n) -> w (Comp(Comp(Shift n, s2), s)) (* MMMM *)

  (* Lift 1 *)
  | Comp(ShiftS s1, ShiftS s2) -> w (ShiftS(Comp (s1, s2)))

  (* Lift 2 *)
  | Comp(Comp(ShiftS s2,s3), s1) -> Comp(s3, ShiftS(Comp(s2, s1)))

  (* LiftEnv *)
  | Comp(Dot(s2,e), ShiftS s1) -> w (Dot(Comp(s2, s1), e))

  (* Added rules for confluence *)
  | Clos (e, Comp (s, EmptyS)) -> w e

  (* Congruence rules *)
  | Clos (Const n, _) -> w (Const n)
  | Clos (Clos (e, s1), s2) -> w (Clos (e, Comp(s2, s1)))
  | Clos (App(e, es), s) -> w (App(Clos(e, s), List.map (fun e-> Clos(e, s)) es))
  | Clos (AppL(e, es), s) -> w (AppL(Clos(e, s), List.map (fun e-> Clos(e, s)) es))
  | Clos (Lam (xs, e), s) -> Lam (xs, Clos (e, List.fold_left (fun s _ -> ShiftS s) s xs))
  | Clos (Set n, s) -> Set n
  | Clos (Star, s) -> Star
  | Clos (Pi(tel, t), s) ->
     let tel' = List.map (fun (i, x, e) -> i, x, Clos (e, s)) tel in
     Pi(tel', Clos (t, s))
  | Clos (SPi(tel, t), s) ->
     let tel', s = cong_stel tel s in
     SPi (tel', Clos (t, s))
  | Clos (Fn (x, e), s) -> Fn (x, Clos(e, s))
  | Clos (Annot (e, t), s) -> Annot (Clos(e,s), Clos(t, s))
  | Clos (e, s) -> let s' = w s in
                   if s = s' then Clos (e, s)
                   else w (Clos (e, s'))
  (* IDK what to do with these *)
  (* | Clos (Under, s) -> assert false *)
  (* | Clos (Snoc (g, x, t), s) -> assert false *)
  (* | Clos (Nil, s) -> assert false *)
  (* | Clos (Box(g, t), s) -> assert false *)
  (* | Clos (Ctx, s) -> assert false *)

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
  Debug.print (fun () -> "Rewrite this " ^ print_exp e
                         ^ "\n===> " ^ print_exp res);
  res


   

open Name
open Syntax
open Syntax.Int
open Print.Int

(* Utilities *)

let rec append_bctx cP cP' =
  match cP with
  | Nil -> cP'
  | CtxVar _ -> raise (Error.Violation "Appended a bctx terminating with a CtxVar to another bctx")
  | Snoc (cP, x, e) -> Snoc (append_bctx cP cP', x, e)

let lookup_bound_name cP x =
  let rec lookup cP0 i =
    match cP0 with
    | Snoc (_, x', t) when x = x' -> i, Clos(t, Shift (i+1), cP)
    | Snoc (cP', _, _) -> lookup cP' (i+1)
    | _ -> raise (Error.Error ("Bound variable " ^ x ^ " not found in bound context"))
  in
  lookup cP 0

let lookup_bound cP (x, j) =
  let proj = function
    | Block bs, Some j' -> snd (Rlist.nth bs j')
    | t, None -> t
    | _ -> raise (Error.Error "Projection of something that is not a block.")
  in
  let rec lookup cP0 i =
    match cP0 with
    | Snoc (_, _, t) when i = 0 -> Clos(proj (t, j), Shift (x+1), cP)
    | Snoc (cP', _, _) -> lookup cP' (i-1)
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup cP x

let rec bctx_of_lam_stel (fs : string list) (tel : stel) (cP : bctx) : bctx * stel=
    match fs, tel with
    | [], tel' -> cP, tel'
    | f::fs', (_, _, t)::tel' ->
       let cP, tel'' = bctx_of_lam_stel fs' tel' cP in
       Snoc (cP , f, t), tel''
    | _, [] -> raise (Error.Error ("Too many variables declared in lambda"))

let bctx_of_stel cP tel =
  let rec make = function
    | [] -> cP
    | (_, x, s)::tel' -> Snoc (make tel', x, s)
  in
  make (List.rev tel)

let rec bctx_of_ctx_exp = function
  | Snoc(g, x, e) -> Snoc(bctx_of_ctx_exp g, x, e)
  | _ -> Nil

let drop_suffix cP n =
    let rec drop cP' n' =
      match cP', n' with
      | _, 0 -> cP'
      | Snoc(cP', _, _), n' -> drop cP' (n'-1)
      | _ -> raise (Error.Error ("Tried to drop " ^ string_of_int n ^ " terms out of " ^ print_bctx cP ^ " which is too short."))
    in
    drop cP n

 let keep_suffix cP n =
    let rec keep cP' n' =
      match cP', n' with
      | _, 0 -> Nil
      | Snoc(cP', x, t), n' -> Snoc(keep cP' (n'-1), x, t)
      | _ -> raise (Error.Error ("Tried to keep " ^ string_of_int n ^ " terms out from " ^ print_bctx cP ^ " which is too short."))
    in
    keep cP n

(* Substitution utilities *)

(* let rec wkn_pat_subst_by_n s = *)
(*   let rec shift = function *)
(*     | CShift n -> CShift (n+1) *)
(*     | CEmpty -> CEmpty *)
(*     | CDot (s, n) -> CDot (shift s, n+1) *)
(*   in *)
(*   function *)
(*   | 0 -> s *)
(*   | n -> wkn_pat_subst_by_n (CDot (shift s , 0)) (n-1) *)

(* let rec lookup_pat_subst err i s = match i, s with *)
(*   | 0, CDot (_, j) -> j *)
(*   | i, CDot (s', _) -> lookup_pat_subst err (i-1) s' *)
(*   | i, CShift n -> (i + n) *)
(*   | i, CEmpty -> raise (Error.Error err) *)


(* let rec comp_pat_subst err s s' = *)
  (* match s, s' with *)
  (* | CShift n, CShift n' -> CShift (n + n') *)
  (* | _, CEmpty -> CEmpty *)
  (* | CEmpty, CShift _ -> raise (Error.Error err) *)
  (* | CEmpty, CDot _ -> raise (Error.Error err) *)
  (* | s, CDot(s', x) -> *)
  (*    CDot(comp_pat_subst err s s', lookup_pat_subst err x s) *)
  (* | CDot (s', x), CShift n -> comp_pat_subst err s' (CShift (n-1)) *)

exception Inv_fail

let apply_inv_pat_subst e s =
  let rec add_id_cdot n s =
    if n = 0 then s
    else CDot(add_id_cdot (n-1) s, (n-1, None))
  in
  let rec apply_inv e s =
    let rec apply_inv' n s cnt =
      match s with
      | CDot (s, m) when n = m -> BVar (cnt, None)
      | CDot (s, _) -> apply_inv' n s (cnt+1)
      | CShift m when fst n < m -> raise Inv_fail
      | CShift m -> BVar (fst n - m, None) (* We lose the projection. Fix plox *)
      | CEmpty -> raise Inv_fail
    in
    match e, s with
    | e, CShift 0 -> e
    | BVar n, _ -> apply_inv' n s 0
    | Star, _ -> Star
    | SPi(tel, t'),_ ->
      SPi(List.map (fun (i,x,e) -> i, x, apply_inv e s) tel, apply_inv t' (add_id_cdot (List.length tel) s))
    | Lam (x, e), _ -> Lam(x, apply_inv e (CDot (s, (0, None))))
    | AppL (e, es), _ -> AppL(apply_inv e s, List.map (fun e -> apply_inv e s) es)
    | SBCtx cP, _ -> SBCtx cP
    | Clos (e, s', cP), _ -> Clos(e, apply_inv s' s, cP)
    | Empty, _ -> Empty
    | Shift n, CShift m when n >= m -> Shift (n - m)
    | Shift n, CShift _ -> raise (Error.Error "Shift too long")
    | Shift n, CEmpty -> Empty
    | Shift n, CDot(_,_) -> assert false

    | Dot (s, e), s' -> Dot (apply_inv s s', apply_inv e s')
    | Comp _, _-> assert false
    | ShiftS _, _-> assert false
    | SCtx t, _ -> SCtx t
    | SConst n, _ -> SConst n
    | Unbox(e, s', cP), _ -> Unbox (e, apply_inv s' s, cP)
    | Block _, _ -> assert false
    | _ -> assert false
  in
  try Some (apply_inv e s)
  with Inv_fail -> None

let apply_inv_subst e s =
  let rec add_id_cdot n s =
    if n = 0 then s
    else Dot(add_id_cdot (n-1) s, BVar (n-1, None))
  in
  let rec apply_inv e s =
    let rec apply_inv' n s cnt =
      match s with
      | Dot (s, BVar m) when n = m -> BVar (cnt, None)
      | Dot (s, _) -> apply_inv' n s (cnt+1)
      | Shift m when fst n < m -> raise Inv_fail
      | Shift m -> BVar (fst n - m, snd n) (* This is suspicious. Please revisit when broken *)
      | Empty -> raise Inv_fail
      | ShiftS _ -> assert false
      | Comp _ -> assert false
      | _ -> raise Inv_fail (* Not a substitution *)
    in
    match e, s with
    | e, Shift 0 -> e
    | BVar n, _ -> apply_inv' n s 0
    | Star, _ -> Star
    | SPi(tel, t'),_ ->
      SPi(List.map (fun (i,x,e) -> i, x, apply_inv e s) tel, apply_inv t' (add_id_cdot (List.length tel) s))
    | Lam (xs, e), _ -> Lam(xs, apply_inv e (ShiftS (List.length xs, s)))
    | AppL (e, es), _ -> AppL(apply_inv e s, List.map (fun e -> apply_inv e s) es)
    | SBCtx cP, _ -> SBCtx cP
    | Clos (e, s', cP), _ -> Clos(e, apply_inv s' s, cP)
    | Empty, _ -> Empty
    | Shift n, Shift m when n >= m -> Shift (n - m)
    | Shift n, Shift _ -> raise (Error.Error "Shift too long")
    | Shift n, Empty -> Empty
    | Shift n, Dot(_,_) -> assert false
    | Shift 0, ShiftS (n, Empty) -> Shift 0

    | Dot (s, e), s' -> Dot (apply_inv s s', apply_inv e s')
    | Comp _, _-> assert false
    | ShiftS _, _-> assert false
    | SCtx t, _ -> SCtx t
    | SConst n, _ -> SConst n
    | Unbox(e, s', cP), _ -> Unbox (e, apply_inv s' s, cP)
    | _ -> raise (Error.Violation ("Failed to apply inverse substitution " ^ print_syn_exp s
                                   ^ " because it was not a substitution."))
  in
  try Some (apply_inv e s)
  with Inv_fail -> None

let rec psubst_of_pat_subst = function
| CShift n -> Shift n
| CEmpty -> Empty
| CDot (s, i) -> Dot (psubst_of_pat_subst s, BVar i)

(* Produces cP' such that cP |- s : cP' *)
let rec shift_cp_inv_pat_subst cP s =
  match cP, s with
  | _, CEmpty -> Nil
  | _, CShift 0 -> cP
  | Snoc (cP', _, _), CShift n  -> shift_cp_inv_pat_subst cP' (CShift (n-1))
  | cP, CDot (s, i) ->
    let t = lookup_bound cP i in
    match apply_inv_pat_subst t s with
    | Some t' -> Snoc (shift_cp_inv_pat_subst cP s, "_", t')
    | None -> raise (Error.Error "Cannot infer substitution")

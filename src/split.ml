open Name
open Syntax
open Sign
open Meta
open MetaSub

module A = Syntax.Apx
module AP = Print.Apx
module I = Syntax.Int
module IP = Print.Int

type single_psubst = name * I.pat
type psubst = single_psubst list

let rec psubst sign (x, p') = function
  | I.PVar n when n = x -> p'
  | I.PVar n -> I.PVar n
  | I.Inacc e -> I.Inacc (subst (x, I.exp_of_pat p') e)
  | I.PConst (n, ps) -> I.PConst (n, List.map (psubst sign (x, p')) ps)
  | I.PPar n when n = x -> raise (Error.Violation "Don't think this can happen")
  | I.PPar n -> I.PPar n
  | I.PBCtx cP -> I.PBCtx (bctx_psubst sign (x, p') cP)
  | I.PUnder -> I.PUnder
  | I.PTBox (cP, p) -> let cP' = subst_bctx (x, I.exp_of_pat p') cP in
                       I.PTBox (cP', syn_psubst sign cP' (x, p') p)
and syn_psubst sign cP (x, p') = function
  | I.PBVar i -> I.PBVar i
  | I.PLam (xs, p) -> I.PLam (xs, syn_psubst sign (bctx_of_lam_pars cP xs) (x, p') p) (* What about shifts in p'? *)
  | I.PSConst (n, ps) -> I.PSConst (n, List.map (syn_psubst sign cP (x, p')) ps)
  | I.PUnbox (n, s, cP') when n = x ->
     begin match p' with
       | I.PVar m -> I.PUnbox (m, s, cP')
       | I.Inacc e -> I.SInacc (e, s, cP')
       | I.PTBox (cP'', q) ->  (* cP' should be equal to cP'' *)
          let rec push_unbox (s, cP') = function
            | I.PBVar i ->
               I.PBVar (lookup_pat_subst ("Expected term " ^ IP.print_syn_pat q ^ " to be closed") i s)
            | I.PLam (xs , p) -> I.PLam(xs, push_unbox (wkn_pat_subst_by_n s (List.length xs), bctx_of_lam_pars cP' xs) p)
            | I.PSConst (n,ps) -> I.PSConst (n, List.map (push_unbox (s, cP')) ps)
            | I.PUnbox (m, s', cP'') ->
               I.PUnbox (m, comp_pat_subst ("Mismatching substitution from term " ^ IP.print_syn_pat q) s s', cP'')
            | I.SInacc (e, s', cP'') ->
               I.SInacc (e, comp_pat_subst ("Mismatching substitution from term " ^ IP.print_syn_pat q) s s', cP'')
            | I.PEmpty  -> I.PEmpty
            | I.PShift n ->
               let rec comp s n =
                 match s, n with
                 | _, 0 ->
                    let rec convert = function
                      | CEmpty -> I.PEmpty
                      | CShift n -> I.PShift n
                      | CDot (s, i) -> I.PDot (convert s, I.PBVar i)
                    in
                    convert s
                 | CDot (s', _), _ -> comp s' (n-1)
                 | CShift n', _ -> I.PShift (n+n')
                 | CEmpty, _ -> raise (Error.Error ("Empty substitution applied to a shift."))
               in
               comp s n
            | I.PDot (sigma, p) -> I.PDot (push_unbox (s, cP') sigma, push_unbox (s, cP') p)
          in
          push_unbox (s, cP') q
       | _ -> assert false
     end
  | I.PUnbox (n, s, cP) -> I.PUnbox (n, s, cP)
  | I.SInacc (e, s, cP) -> I.SInacc (subst (x, I.exp_of_pat p') e, s, cP)
  | I.PEmpty -> I.PEmpty
  | I.PShift n -> I.PShift n
  | I.PDot (s, p) -> I.PDot (syn_psubst sign cP (x, p') s, syn_psubst sign cP (x, p') p)

and bctx_psubst sign (x, p') = function
  | I.PNil -> I.PNil
  | I.PSnoc (cP, s, t) -> I.PSnoc (bctx_psubst sign (x, p') cP, s, subst_syn (x, I.exp_of_pat p') t)
  | I.PCtxVar n when n = x ->
     begin match p' with
     | I.PBCtx p -> p
     | I.PVar m -> I.PCtxVar m
     | _ -> raise (Error.Violation ("Why not?" ^ IP.print_pat p'))
     end
  | I.PCtxVar n -> I.PCtxVar n

let rec compose_single_with_psubst sign s = function
  | [] -> []
  | (y, t') :: sigma -> (y, psubst sign s t') :: (compose_single_with_psubst sign s sigma)

let pats_of_psubst : psubst -> I.pats = List.map (fun (x, p) -> p)

let simul_psubst sign sigma p =
  List.fold_left (fun p s -> psubst sign s p) p sigma

let simul_syn_psubst sign cP sigma p =
  List.fold_left (fun p s -> syn_psubst sign cP s p) p sigma

let simul_psubst_on_list sign sigma ps =
  List.map (simul_psubst sign sigma) ps

let simul_syn_psubst_on_list sign cP sigma ps =
  List.map (simul_syn_psubst sign cP sigma) ps

let rec check_match (q : I.pat) (p : A.pat) =
  match q, p with
  | I.PVar n, _ -> true
  | I.PPar n, A.PPar n' -> true
  | I.PConst (n, qs), A.PConst (n', ps) when n = n' -> check_all qs ps
  | I.PConst (n, qs), A.PConst (n', ps) -> false
  | I.Inacc _, _ -> true
  | I.PBCtx q, _ -> bctx_check_match q p
  | I.PTBox (cP, q), p -> syn_check_match cP q p
  | _ -> false
and syn_check_match cP q p =
  match q, p with
  | I.PLam (xs, q), A.PLam (ys, p) -> syn_check_match (bctx_of_lam_pars cP xs) q p
  | I.PUnbox (n, s, cP'), A.PClos (m, s') when s = s' -> true
  | I.PUnbox (n, s, cP'), _ -> true
  | I.SInacc _, _ -> true
  | I.PEmpty, A.PEmpty -> true
  | I.PShift n, A.PShift n' when n = n' -> true
  | I.PBVar i, A.PBVar i' when i = i' -> true
  | I.PSConst (n, qs), A.PConst (n', ps) when n = n' -> List.for_all2 (syn_check_match cP) qs ps
  | I.PSConst (n, ps), A.PConst (n', qs) -> false
  | I.PDot (s, q'), A.PDot (s', p') -> syn_check_match cP s s' && syn_check_match cP q' p'
  | _ -> false
and bctx_check_match q p =
  match q, p with
  | I.PCtxVar x, A.PVar y  -> true
  | I.PSnoc (q1, _, q2), A.PSnoc (p1, _, p2) -> bctx_check_match q1 p1 (* @ (syn_check_match (I.bctx_of_pat_ctx p1) p2 q2) *)
  | I.PNil, A.PNil -> true
  | _ -> false
and check_all qs ps =
  Debug.print (fun () -> "Il entreprit un long voyage."); List.for_all2 check_match qs ps

let rec rename (q : I.pat) (p : A.pat) : (name * name) list =
  match q,p with
  | I.PVar n, A.PVar m -> [n, m]
  | I.PPar n, A.PPar m -> [n, m]
  | I.PConst (_, qs), A.PConst (_, ps) -> rename_all qs ps
  | I.PBCtx cP, p -> []
  | I.PUnder, A.PUnder -> []
  | I.PTBox (cP, q), p -> rename_syn q p
  | _ -> raise (Error.Violation "Renaming of tree node expects matching pattern with tree node")

and rename_syn (q : I.syn_pat) (p : A.pat) : (name * name) list =
  match q, p with
  | I.PBVar _, A.PBVar _ -> []
  | I.PLam (es, q), A.PLam (sl, p) -> rename_syn q p
  | I.PSConst (_, qs), A.PConst (_, ps) -> rename_all_syn qs ps
  | I.PUnbox (n, _, _), A.PVar m -> [n, m]
  | I.SInacc _, A.Inacc _ -> []
  | I.PEmpty, A.PEmpty -> []
  | I.PShift _, A.PShift _ -> []
  | I.PDot(sq, q), A.PDot (sp, p) -> rename_syn sq sp @ rename_syn q p
  | _ -> raise (Error.Violation "Renaming of tree node expects matching pattern with tree node")

and rename_all (qs : I.pats) (ps : A.pats) : (name * name) list = List.concat (List.map2 rename qs ps)

and rename_all_syn (qs : I.syn_pats) (ps : A.pats) : (name * name) list = List.concat (List.map2 rename_syn qs ps)

let is_blocking = function
  | A.PVar _
  | A.PWildcard
  | A.Inacc _ -> false
  | _ -> true

let rec choose_blocking_var (qs : I.pats) (ps : A.pats) : (name * A.pat) option =
  match qs, ps with
  | [], [] -> None
  | I.PVar n :: qs', p :: ps' when is_blocking p -> Some (n, p)
  | q :: qs', p :: ps' -> choose_blocking_var qs' ps'
  | _ -> assert false

let inac_subst = List.map (fun (x, e) -> x, I.Inacc e)
let pvar_list_of_ctx : I.ctx -> I.pats = List.map (fun (x, _) -> I.PVar x)
let psubst_of_names = List.map (fun (n, m) -> n, I.PVar m)
let subst_of_names = List.map (fun (n, m) -> n, I.Var m)

let rec get_splits (sign : signature) (cD : I.ctx) (qs : I.pats) (n, p : name * A.pat) : (I.ctx * I.pats * I.subst) option list =
  let t = try List.assoc n cD
    with Not_found -> raise (Error.Violation ("Pattern " ^ IP.print_pats qs
                             ^ " has name not in context " ^ IP.print_ctx cD))
  in
  let ct, sp = match Whnf.whnf sign t with
    | I.Box _ -> raise Error.NotImplemented
    | I.Const c -> c, []
    | I.App (I.Const c, sp) -> c, sp
    | _ -> raise (Error.Error "Cannot split on this constructor")
  in
  let cs = lookup_constructors sign ct in
  let rec unify = function
    | [] -> []
    | (c, tel, ts) :: cs' ->
      let cG = ctx_of_tel tel in
      let cD' = cD @ cG in
      let flex = List.map fst cD' in
      try let cD'', sigma = Unify.unify_flex_many (sign, cD') flex ts sp in
          Debug.print (fun () -> "Unification of ts " ^ IP.print_exps ts
            ^ "\nwith sp " ^ IP.print_exps sp
            ^ "\nmoving context cD' = " ^ IP.print_ctx cD'
            ^ "\nto context " ^ IP.print_ctx cD'');
          let psigma = inac_subst sigma in
          let s = n, I.App (I.Const c, simul_subst_on_list sigma (var_list_of_ctx cG)) in
          let psigma' = (n, I.PConst (c, simul_psubst_on_list sign psigma (pvar_list_of_ctx cG))) :: psigma in
          let cD''' = ctx_subst s (List.filter (fun (x, _) -> x <> n) cD'') in
          Some (cD''', simul_psubst_on_list sign psigma' qs, s :: sigma) :: unify cs'

      with Unify.Unification_failure msg ->
        Debug.print (fun () -> "Splitting on constructor " ^ c
          ^ " resulted in unification failure\n"
          ^ Unify.print_unification_problem msg);
        None :: unify cs'
  in
  unify cs

(* If type of pattern match function is tau, then
   tau = cG * t for some spine cG.
   cD |- sigma : cG
   . |- qs => cD

   cD' |- sigma' cD
   . |- ps => cD'
 *)
let rec split (sign : signature) (cD : I.ctx) (qs : I.pats) (sigma : I.subst)
    (ps, rhs : A.pats * A.rhs) (t : I.exp) : I.split_tree =
  Debug.print(fun () -> "Splitting qs = " ^ IP.print_pats qs
    ^ "\nagainst ps = " ^ AP.print_pats ps);
  match choose_blocking_var qs ps with
  | None ->
    let s = rename_all qs ps in
    let qs = simul_psubst_on_list sign (psubst_of_names s) qs in
    let sigma' = subst_of_names s in
    let sigma'' = sigma @ sigma' in  (* we apply sigma first, then sigma' *)
    let rec subst_name n = function
      | (n', m) :: sigma when n = n' -> m
      | _ :: sigma -> subst_name n sigma
      | [] -> n                         (* name stays the same *)
    in
    let rec subst_ctx = function
      | (n, e) :: cD -> (subst_name n s, simul_subst sigma e) :: subst_ctx cD
      | [] -> []
    in
    let cD' = subst_ctx cD in
  (* Need to check inaccessible? *)
    let rhs' = match rhs with
      | A.Just e -> I.Just (Recon.check (sign, cD') e (simul_subst sigma'' t))
      | A.Impossible n -> I.Impossible n (* Need to check if actually impossible *)
    in
    I.Leaf (cD', qs, sigma'', rhs')
  | Some (n, p) ->
    Debug.print (fun () -> "Found blocking variable " ^ print_name n);
    let f = function
      | None -> assert false
      (* todo: figure out impossible branches for specific constructors *)
      | Some (cD', qs', sigma') ->
        if check_all qs' ps then
          split sign cD' qs' sigma' (ps, rhs) (simul_subst sigma t)
        else
          I.Incomplete (cD', qs', sigma')
    in
    I.Node (cD, qs, sigma, n, List.map f (get_splits sign cD qs (n, p)))

exception Backtrack

let rec navigate (sign : signature) (t : I.exp) (tr : I.split_tree) (ps, rhs : A.pats * A.rhs) : I.split_tree =
  Debug.print(fun () -> "Il était un petit navire.");
  match tr with
  | I.Incomplete (cD, qs, sigma) ->
    if check_all qs ps then
      split sign cD qs sigma (ps, rhs) t
    else
      raise Backtrack
  | I.Node (cD, qs, sigma, n, tr') ->
    if check_all qs ps then
      let rec f = function
        | [] -> raise (Error.Error "No valid branch found")
        | tr :: trs ->
          try navigate sign (simul_subst sigma t) tr (ps, rhs)
          with Backtrack -> f trs
      in f tr'
    else
      raise Backtrack
  | I.Leaf (cD, qs, _, _) ->
    if check_all qs ps then
      raise (Error.Error ("Branch " ^ IP.print_pats qs ^ " cannot be reached."))
    else
      raise Backtrack

let check_clauses (sign : signature) (f : def_name) (telG : I.tel) (t : I.exp) (ds : A.pat_decls) : I.split_tree =
  (* we add a non-reducing version of f to the signature *)
  let sign' =  (PSplit (f, telG, t, EmptyTree, Stuck)) :: sign in
  let cD = ctx_of_tel telG in
  let qs = List.map (fun (n, t) -> I.PVar n) cD in
  List.fold_left (navigate sign' t) (I.Incomplete (cD, qs, [])) ds

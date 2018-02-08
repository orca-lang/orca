(* Meta operations on the AST, like substitutions and free vars *)

open Util
open Name
open Sign
open Print
open Print.Int
open Syntax
open Syntax.Int

let rec in_ctx n = function
  | (x, _) :: _ when x = n -> true
  | _ :: cG -> in_ctx n cG
  | [] -> false

let rec fv cG =
  let fv e = fv cG e in
  function
  | Set _ -> []
  | Ctx sch -> fv_schema cG sch
  | BCtx cP -> fv_ctx cG cP
  | Pi (tel, t) -> fv_pi cG tel t
  | Box (ctx, e) -> fv_ctx cG ctx @ fv_syn cG e
  | TermBox (ctx, e) -> fv_ctx cG ctx @ fv_syn cG e
  | Fn (xs, e) ->
     List.fold_left (fun vars x -> vars -- x) (fv e) xs
  | App (e1, es) -> fv e1 @ List.concat (List.map fv es)
  | Const n -> []
  | Var n when in_ctx n cG -> []
  | Var n -> [n]
  | Annot (e1, e2) -> fv e1 @ fv e2
  | Hole _ -> []

and fv_syn cG =
  let fvs e = fv_syn cG e in
  function
  | Star -> []
  | SPi (tel, e) -> fv_spi cG tel e
  | Lam (x, e) -> fvs e
  | AppL (e, es) -> fvs e @ List.concat (List.map fvs es)
  | SConst _ -> []
  | BVar i -> []
  | Clos (e1, e2, _) -> fvs e1 @ fvs e2
  | Empty -> []
  | Shift n -> []
  | Comp (e1, _, e2)
  | Dot (e1, e2) -> fvs e1 @ fvs e2
  | ShiftS (_, e) -> fvs e
  | Unbox (e, s, cP) ->
     fv cG e @ fvs s @ fv_ctx cG cP
  | SBCtx cP -> fv_ctx cG cP
  | SCtx sch -> fv_schema cG sch
  | Block block -> List.concat (Rlist.mapl (fun (_, t) -> fvs t) block)

and fv_schema cG = function
  | Schema (impl, expl) -> snd (List.fold_left (fun (cG, names) (n, cP, t) -> (n,Box(cP, t)) :: cG,
                                                                                 fv cG (Box(cP, t)) @ names)
                                                  (cG, []) impl)
                           @ List.concat (List.map (fun (_, t) -> fv_syn cG t) expl)

and fv_ctx cG = function
  | Nil -> []
  | Snoc(cP, _, e) -> fv_ctx cG cP @ fv_syn cG e
  | CtxVar n when in_ctx n cG -> []
  | CtxVar n -> [n]

and fv_pi cG (tel : tel) (t : exp) = match tel with
  | [] -> fv cG t
  | (_, n, e)::tel -> fv cG e @ (fv_pi cG tel t -- n)

and fv_spi cG (tel : stel) (t : syn_exp) = match tel with
  | [] -> fv_syn cG t
  | (_, n, e)::tel -> fv_syn cG e @ (fv_spi cG tel t)

let rec fv_pat =
  function
  | PVar n -> [n]
  | Inacc _ -> []
  | PConst (n, ps) -> fv_pats ps
  | PBCtx cP -> fv_pat_bctx cP
  | PUnder -> []
  | PTBox (cP, p) -> fv_syn_pat p (* MMMM *)

and fv_syn_pat =
  function
  | PBVar i -> []
  | PPar n -> [n]
  | PLam (f, p) -> fv_syn_pat p
  | PSConst (n, ps) -> fv_syn_pats ps
  | PUnbox (n, _, _) -> [n]
  | SInacc (_, _, _) -> []
  | PEmpty -> []
  | PShift i -> []
  | PDot (p1, p2) -> fv_syn_pat p1 @ fv_syn_pat p2

and fv_pat_bctx =
  function
  | PNil -> []
  | PSnoc (cP, _, _) -> fv_pat_bctx cP
  | PCtxVar n -> [n]

and fv_pats ps = List.concat(List.map fv_pat ps)
and fv_syn_pats ps = List.concat(List.map fv_syn_pat ps)

(* Generate fresh names for all the bound variables,
     to keep names unique *)

let rec refresh_exp (rep : (name * name) list) : exp -> exp =
  let f x = refresh_exp rep x in
  function
  | Set n -> Set n

  | Ctx sch -> Ctx (refresh_schema rep sch)

  | Pi (tel, t) -> let tel', t' = refresh_tel rep tel t in Pi(tel', t')

  | Box (cP, e) -> Box(refresh_bctx rep cP, refresh_syn_exp rep e)
  | TermBox (cP, e) -> TermBox(refresh_bctx rep cP, refresh_syn_exp rep e)
  | BCtx cP -> BCtx (refresh_bctx rep cP)
  | Fn (xs, e) ->
     let xs' = List.map refresh_name xs in
     let extra = List.map2 (fun x y -> x, y) xs xs' in
     Fn (xs', refresh_exp (extra @ rep) e)
  | App (e1, es) -> App(f e1, List.map f es)
  | Const n -> Const n
  | Var n ->
     begin try
         Var (List.assoc n rep)
       with
         Not_found -> Var n
     end
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s

and refresh_syn_exp rep =
  let f x = refresh_syn_exp rep x in
  function
  | Star -> Star
  | SCtx sch -> SCtx (refresh_schema rep sch)
  | SPi (tel, t) -> let tel', t' = refresh_stel rep tel t in SPi(tel', t')
  | Lam (x, e) ->
     Lam(x, f e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar i -> BVar i
  | Clos (e1, e2, cP) -> Clos(f e1, f e2, refresh_bctx rep cP)
  | Empty -> Empty
  | Shift n -> Shift n
  | Comp (e1, cP, e2) -> Comp (f e1, refresh_bctx rep cP, f e2)
  | ShiftS (n, e) -> ShiftS (n, f e)
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | Unbox (e1, e2, cP) -> Unbox (refresh_exp rep e1, f e2, refresh_bctx rep cP)
  | SBCtx cP -> SBCtx (refresh_bctx rep cP)
  | Block bs -> Block (Rlist.map (fun (n, t) -> (n, f t)) bs)

and refresh_schema rep (Schema (im, ex)) =
  let f (n, t) = (n, refresh_syn_exp rep t) in
  Schema (List.fold_left
               (fun (acc, rep) (n, cP, t) ->
                 let n' = refresh_name n in
                 (n', refresh_bctx rep cP, refresh_syn_exp rep t) :: acc, (n,n')::rep)
               ([], rep) im |> fst, List.map f ex)

and refresh_bctx (rep : (name * name) list) : bctx -> bctx =
  function
  | Snoc (cP, x, e) -> Snoc (refresh_bctx rep cP, x, refresh_syn_exp rep e)
  | Nil -> Nil
  | CtxVar n ->
     begin try
         CtxVar (List.assoc n rep)
       with
         Not_found -> CtxVar n
     end

and refresh_tel (rep : (name * name) list) (tel : tel) (t : exp) : tel * exp =
  match tel with
  | [] -> [], refresh_exp rep t
  | (i, n, e) :: tel ->
     let n' = refresh_name n in
     let tel', t' = refresh_tel ((n, n')::rep) tel t in
     ((i, n', refresh_exp rep e)::tel'), t'

and refresh_stel (rep : (name * name) list) (tel : stel) (t : syn_exp) : stel * syn_exp =
  match tel with
  | [] -> [], refresh_syn_exp rep t
  | (i, n, e) :: tel ->
     let tel', t' = refresh_stel rep tel t in
     ((i, n, refresh_syn_exp rep e)::tel'), t'

let refresh (e : exp) : exp = refresh_exp [] e

(* refresh one free variable *)
let rec refresh_free_var (x , y : name * name) (e : exp) : exp =
  let f e = refresh_free_var (x, y) e in
  match e with
  | Set n -> Set n
  | Ctx sch -> Ctx (refresh_free_var_schema (x, y) sch)
  | Pi (tel, t) ->
     let tel', t' = refresh_free_var_tel (x, y) tel t in
     Pi (tel', t')
  | Box (cP, e) -> Box(refresh_free_var_bctx (x, y) cP, refresh_free_var_syn (x, y) e)
  | TermBox (cP, e) -> TermBox(refresh_free_var_bctx (x, y) cP, refresh_free_var_syn (x, y) e)
  | BCtx cP -> BCtx (refresh_free_var_bctx (x, y) cP)
  | Fn (xs, _) when List.mem x xs -> raise (Error.Violation "Duplicate variable name")
  | Fn (xs, e) -> Fn (xs, f e)
  | App (e1, es) -> App(f e1, List.map f es)
  | Const n -> Const n
  | Var n when n = x -> Var y
  | Var n -> Var n
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s

and refresh_free_var_syn (x, y) e =
  let f e = refresh_free_var_syn (x, y) e in
  match e with
  | Star -> Star
  | SCtx sch -> SCtx (refresh_free_var_schema (x, y) sch)
  | SPi (tel, t) ->
     let tel', t' = refresh_free_var_stel (x, y) tel t in
     SPi (tel', t')
  | Lam (x, e) -> Lam(x, f e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | BVar i -> BVar i
  | SConst n -> SConst n
  | Clos (e1, e2, cP) -> Clos(f e1, f e2, refresh_free_var_bctx (x, y) cP)
  | Unbox (e1, e2, cP) -> Unbox(refresh_free_var (x, y) e1, f e2, refresh_free_var_bctx (x, y) cP)
  | Empty -> Empty
  | Shift n -> Shift n
  | Comp (e1, cP, e2) -> Comp (f e1, refresh_free_var_bctx (x, y) cP, f e2)
  | ShiftS (n, e) -> ShiftS (n, f e)
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | SBCtx cP -> SBCtx (refresh_free_var_bctx (x, y) cP)
  | Block cs -> Block (Rlist.map (fun (z, e) -> (z, f e)) cs) (* z has to be free *)

and refresh_free_var_schema (x, y as rep) (Schema (im, ex)) =
  let f (n, cP, t) =
    if n <> x then
      (n, refresh_free_var_bctx rep cP, refresh_free_var_syn rep t)
    else
      raise (Error.Violation "Duplicate name in refresh_free_var_schema") in
  let g (n, t) = (n, refresh_free_var_syn rep t) in
  Schema (List.map f im, List.map g ex)

and refresh_free_var_bctx (x, y) cP =
  match cP with
  | Snoc (cP, z, e2) -> Snoc(refresh_free_var_bctx (x, y) cP , z, refresh_free_var_syn (x, y) e2)
  | Nil -> Nil
  | CtxVar n when n = x -> CtxVar y
  | CtxVar n -> CtxVar n

and refresh_free_var_tel (x, y) tel t =
  match tel with
  | [] -> [], refresh_free_var (x, y) t
  | (i, n, e) :: tel when n = x ->  raise (Error.Violation "Duplicate variable name")
  | (i, n, e) :: tel ->
     let tel', t' = refresh_free_var_tel (x, y) tel t in
     (i, n, refresh_free_var (x, y) e) :: tel', t'
and refresh_free_var_stel (x, y) tel t =
  match tel with
  | [] -> [], refresh_free_var_syn (x, y) t
  | (i, n, e) :: tel ->
     let tel', t' = refresh_free_var_stel (x, y) tel t in
     (i, n, refresh_free_var_syn (x, y) e) :: tel', t'


let refresh_free_vars (rep : (name * name) list) e =
  List.fold_left (fun e (y, y') -> refresh_free_var (y, y') e) e rep

(* Operations on terms *)

(* Substitution of regular variables *)

let fv_subst cG sigma = List.concat (List.map (fun (n, e) -> fv cG e -- n) sigma)

let rec subst (x, es : single_subst) (e : exp) :  exp =
  let f e = subst (x, es) e in
  match e with
  | Set n -> Set n
  | Ctx sch -> Ctx (sub_schema (x, es) sch)
  | Pi (tel, t) ->
     let tel', t' = subst_pi (x, es) tel t in
     Pi(tel', t')
  | Box (ctx, e) -> Box(subst_bctx (x, es) ctx, subst_syn (x, es) e)
  | TermBox (ctx, e) -> TermBox(subst_bctx (x, es) ctx, subst_syn (x, es) e)
  | BCtx cP -> BCtx(subst_bctx (x, es) cP)
  | Fn (ys, e) ->
     let ys' = List.map refresh_name ys in
     (* the following cannot happen because y' is just fresh *)
     (* if List.mem y' (fv es) then raise (Error.Violation
       "Duplicate variable name would be captured.") ; *)
     let extra = List.map2 (fun x y -> x, y) ys ys' in
     Fn(ys', subst (x, es) (refresh_free_vars extra e))

  | App (e1, es) -> App(f e1, List.map f es)
  | Const n -> Const n
  | Var n  when x = n -> refresh es
  | Var n -> Var n
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s

and sub_schema s (Schema (im, ex)) =
  let f (n, cP, e) = (n, subst_bctx s cP, subst_syn s e) in
  let g (n, e) = (n, subst_syn s e) in
  Schema (List.map f im, List.map g ex)

and subst_syn (x, es) e =
  let f e = subst_syn (x, es) e in
  match e with
  | Star -> Star
  | SCtx sch -> SCtx (sub_schema (x, es) sch)
  | SPi (tel, t) ->
     let tel', t' = subst_spi (x, es) tel t in
     SPi(tel', t')
  | Lam (x, e) -> Lam(x, f e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar i -> BVar i
  | Clos (e1, e2, cP) -> Clos(f e1, f e2, subst_bctx (x, es) cP)
  | Unbox (e1, e2, cP) -> Unbox(subst (x, es) e1, f e2, subst_bctx (x, es) cP)
  | Empty -> Empty
  | Shift n -> Shift n
  | ShiftS (n, e) -> ShiftS (n, f e)
  | Comp (e1, cP, e2) -> Comp (f e1, subst_bctx (x, es) cP, f e2)
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | SBCtx cP -> SBCtx (subst_bctx (x, es) cP)
  | Block cs -> Block (Rlist.map (fun (y, e) -> (y, subst_syn (x, es) e)) cs)

and subst_bctx (x, es : single_subst) cP =
  match cP with
  | Snoc (e1, y, e2) -> Snoc (subst_bctx (x, es) e1, y, subst_syn (x, es) e2)
  | Nil -> Nil
  | CtxVar n when x = n ->
     begin match es with
     | BCtx cP -> refresh_bctx [] cP
     | Var y -> CtxVar y
     | e -> raise (Error.Violation ("I don't believe you! " ^ print_exp e))
     end
  | CtxVar n -> CtxVar n

and subst_pi (x, es) tel t =
  match tel with
  | [] -> [], subst (x, es) t
  | (i, n, e) :: tel ->
     let n' = refresh_name n in
     (* the following cannot happen because n' is just fresh *)
     (* if List.mem n' (fv es) then raise (Error.Violation "Duplicate variable name would be captured.") ; *)
     let tel', t' = refresh_free_var_tel (n, n') tel t in
     let tel'', t'' = subst_pi (x, es) tel' t' in
     (i, n', subst (x, es) e) :: tel'', t''
and subst_spi (x, es) tel t =
  match tel with
  | [] -> [], subst_syn (x, es) t
  | (i, n, e) :: tel ->
     let tel', t' = subst_spi (x, es) tel t in
     (i, n, subst_syn (x, es) e) :: tel', t'

let simul_subst sigma e =
  List.fold_left (fun e s -> subst s e) e sigma

let simul_subst_syn sigma e =
  List.fold_left (fun e s -> subst_syn s e) e sigma

let simul_subst_on_list sigma l =
  List.map (fun e -> simul_subst sigma e) l

let simul_subst_syn_on_list sigma l =
  List.map (fun e -> simul_subst_syn sigma e) l

let simul_subst_on_tel sigma tel =
  List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

let simul_subst_on_stel sigma tel =
  List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

let simul_subst_on_bctx sigma cP =
  List.fold_left (fun cP s -> subst_bctx s cP) cP sigma

let rec compose_single_with_subst s = function
  | [] -> []
  | (y, t') :: sigma -> (y, subst s t') :: (compose_single_with_subst s sigma)

let compose_subst sigma delta = List.map (fun (x, t) -> x, simul_subst sigma t) delta

let rec subst_of_pats sign (sigma : pats) (tel : tel) : subst =
  match sigma, tel with
  | [], [] -> []
  | p :: ps, (_, n, t) :: tel' -> (n, exp_of_pat p) :: (subst_of_pats sign ps tel')
  | _ -> raise (Error.Violation "subst_of_ctx_map got lists of different lengths")

let ctx_of_tel (tel : tel) : ctx = List.rev (List.map (fun (_, x, s) -> x, s) tel)

let exp_list_of_ctx : ctx -> exp list = List.map snd

let subst_of_ctx : ctx -> subst = List.map (fun (x, _) -> x, Var x)

let name_list_of_ctx : ctx -> name list = List.map fst

let var_list_of_ctx : ctx -> exp list = List.map (fun (x, _) -> Var x)

let var_list_of_tel : tel -> exp list = List.map (fun (_, x, _) -> Var x)


let unbox_list_of_ctx cP : ctx -> syn_exp list = List.map (fun (x, _) -> Unbox(Var x, id_sub, cP))
let punbox_list_of_ctx cP : ctx -> syn_pat list = List.map (fun (x, _) -> PUnbox(x, pid_sub, cP))
let unbox_list_of_tel cP : tel -> syn_exp list = List.map (fun (_, x, _) -> Unbox(Var x, id_sub, cP))
let punbox_list_of_tel cP : tel -> syn_pat list = List.map (fun (_, x, _) -> PUnbox(x, pid_sub, cP))


let rec ctx_subst s = function
  | (x, t) :: cG -> (x, subst s t) :: (ctx_subst s cG)
  | [] -> []

let shift_subst_by_ctx sigma cG =
  let sigma' = sigma @ (List.map (fun (x, _) -> x, Var x) cG) in
  Debug.print (fun () -> "Shift called with sigma = " ^ print_subst sigma
                         ^ "\ncG = " ^ print_ctx cG
                         ^ "\nresulting in " ^ print_subst sigma'
                         ^ ".");
  sigma'

let simul_subst_on_ctx sigma =
    List.map (fun (x, e) -> x, simul_subst sigma e)

let lookup_ctx cG n =
  try
    Some (List.assoc n cG)
  with
    Not_found -> None

let lookup_ctx_fail cG n =
  match lookup_ctx cG n with
  | None -> raise (Error.Violation
                     ("Unbound var after preprocessing, this cannot happen. (Var: "
                      ^ print_name n ^ ")"))
  | Some t -> t

let rec rename_ctx_using_subst (cG : ctx) (sigma : subst) =
  match cG with
  | [] -> []
  | (x, t) :: cG' ->
     match lookup_ctx sigma x with
     | Some (Var y) -> (y, t) :: (rename_ctx_using_subst cG' sigma)
     | _ -> (x, t) :: (rename_ctx_using_subst cG' sigma)

let print_subst sigma = "[" ^ String.concat ", " (List.map (fun (x, e) -> print_exp e ^ "/" ^ print_name x) sigma) ^ "]"


(* Operations on patterns *)

let bctx_of_lam_pars cP xs = List.fold_left (fun cP (x, t) -> Snoc(cP, x, t)) cP xs

(* Substitution utilities *)

let rec wkn_pat_subst_by_n s =
  let rec shift = function
    | CShift n -> CShift (n+1)
    | CEmpty -> CEmpty
    | CDot (s, n) -> CDot (shift s, (fst n+1, snd n))
  in
  function
  | 0 -> s
  | n -> wkn_pat_subst_by_n (CDot (shift s, zidx)) (n-1)

let rec lookup_pat_subst err i s = match i, s with
  | (0, _), CDot (_, j) -> j
  | i, CDot (s', _) -> lookup_pat_subst err (dec_idx i) s'
  | i, CShift n -> shift_idx i n
  | i, CEmpty -> raise (Error.Error err)

let rec comp_pat_subst err s s' =
  match s, s' with
  | CShift n, CShift n' -> CShift (n + n')
  | _, CEmpty -> CEmpty
  | CEmpty, CShift _ -> raise (Error.Error err)
  | CEmpty, CDot _ -> raise (Error.Error err)
  | s, CDot(s', x) ->
     CDot(comp_pat_subst err s s', lookup_pat_subst err x s)
  | CDot (s', x), CShift n -> comp_pat_subst err s' (CShift (n-1))

type single_psubst = name * pat
type psubst = single_psubst list

let rec psubst sign (x, p') = function
  | PVar n when n = x -> p'
  | PVar n -> PVar n
  | Inacc e -> Inacc (subst (x, exp_of_pat p') e)
  | PConst (n, ps) -> PConst (n, List.map (psubst sign (x, p')) ps)
  | PBCtx cP -> PBCtx (bctx_psubst sign (x, p') cP)
  | PUnder -> PUnder
  | PTBox (cP, p) -> let cP' = subst_bctx (x, exp_of_pat p') cP in
                       PTBox (cP', syn_psubst sign cP' (x, p') p)
and syn_psubst sign cP (x, p') = function
  | PBVar i -> PBVar i
  | PLam (xs, p) -> PLam (xs, syn_psubst sign (bctx_of_lam_pars cP xs) (x, p') p) (* What about shifts in p'? *)
  | PSConst (n, ps) -> PSConst (n, List.map (syn_psubst sign cP (x, p')) ps)
  | PUnbox (n, s, cP') when n = x ->
     begin match p' with
       | PVar m -> PUnbox (m, s, cP')
       | Inacc e -> SInacc (e, s, cP')
       | PTBox (cP'', q) ->  (* cP' should be equal to cP'' *)
          let rec push_unbox (s, cP') = function
            | PBVar i ->
               PBVar (lookup_pat_subst ("Expected term " ^ print_syn_pat q ^ " to be closed") i s)
            | PLam (xs , p) -> PLam(xs, push_unbox (wkn_pat_subst_by_n s (List.length xs), bctx_of_lam_pars cP' xs) p)
            | PSConst (n,ps) -> PSConst (n, List.map (push_unbox (s, cP')) ps)
            | PUnbox (m, s', cP'') ->
               PUnbox (m, comp_pat_subst ("Mismatching substitution from term " ^ print_syn_pat q) s s', cP'')
            | SInacc (e, s', cP'') ->
               SInacc (e, comp_pat_subst ("Mismatching substitution from term " ^ print_syn_pat q) s s', cP'')
            | PEmpty  -> PEmpty
            | PShift n ->
               let rec comp s n =
                 match s, n with
                 | _, 0 ->
                    let rec convert = function
                      | CEmpty -> PEmpty
                      | CShift n -> PShift n
                      | CDot (s, i) -> PDot (convert s, PBVar i)
                    in
                    convert s
                 | CDot (s', _), _ -> comp s' (n-1)
                 | CShift n', _ -> PShift (n+n')
                 | CEmpty, _ -> raise (Error.Error ("Empty substitution applied to a shift."))
               in
               comp s n
            | PDot (sigma, p) -> PDot (push_unbox (s, cP') sigma, push_unbox (s, cP') p)
            | PPar n -> PPar n

          in
          push_unbox (s, cP') q
       | _ -> assert false
     end
  | PUnbox (n, s, cP) -> PUnbox (n, s, cP)
  | SInacc (e, s, cP) -> SInacc (subst (x, exp_of_pat p') e, s, cP)
  | PEmpty -> PEmpty
  | PShift n -> PShift n
  | PDot (s, p) -> PDot (syn_psubst sign cP (x, p') s, syn_psubst sign cP (x, p') p)
  | PPar n when n = x ->
    begin match p' with
    | PVar m -> PUnbox (m, pid_sub, cP)
    | Inacc e -> SInacc (e, pid_sub, cP)
    | PTBox (cP', q) -> assert false
    | _ -> assert false
    end
  | PPar n -> PPar n


and bctx_psubst sign (x, p') = function
  | PNil -> PNil
  | PSnoc (cP, s, t) -> PSnoc (bctx_psubst sign (x, p') cP, s, subst_syn (x, exp_of_pat p') t)
  | PCtxVar n when n = x ->
     begin match p' with
     | PBCtx p -> p
     | PVar m -> PCtxVar m
     | _ -> raise (Error.Violation ("Why not?" ^ print_pat p'))
     end
  | PCtxVar n -> PCtxVar n

let rec compose_single_with_psubst sign s = function
  | [] -> []
  | (y, t') :: sigma -> (y, psubst sign s t') :: (compose_single_with_psubst sign s sigma)

let pats_of_psubst : psubst -> pats = List.map (fun (x, p) -> p)

let simul_psubst sign sigma p =
  List.fold_left (fun p s -> psubst sign s p) p sigma

let simul_syn_psubst sign cP sigma p =
  List.fold_left (fun p s -> syn_psubst sign cP s p) p sigma

let simul_psubst_on_list sign sigma ps =
  List.map (simul_psubst sign sigma) ps

let simul_syn_psubst_on_list sign cP sigma ps =
  List.map (simul_syn_psubst sign cP sigma) ps

let inac_subst e = List.map (fun (x, e) -> x, Inacc e) e
let pvar_list_of_tel : tel -> pats = List.map (fun (_, x, _) -> PVar x)
let punbox_list_of_tel cP : tel -> syn_pat list = List.map (fun (_, x, _) -> PUnbox(x, pid_sub, cP))
let psubst_of_names e = List.map (fun (n, m) -> n, PVar m) e
let subst_of_names e = List.map (fun (n, m) -> n, Var m) e


let rec rename (q : pat) (p : Apx.pat) : (name * name) list =
  match q,p with
  | PVar n, Apx.PVar m -> [n, m]
  | PConst (_, qs), Apx.PConst (_, ps) -> rename_all qs ps
  | PBCtx cP, p -> []
  | PUnder, Apx.PUnder -> []
  | PTBox (cP, q), p -> rename_syn q p
  | Inacc (Var n), Apx.PVar m -> [n, m]
  | PVar n, Apx.Inacc (Apx.Var m) -> [n, m]
  | Inacc _, _ -> []                  (* can this be possible? *)
  | _, Apx.Inacc _ -> []                    (* Should we do that here or in a check_inacc function? *)
  | _, Apx.PWildcard -> []
  | _ -> raise (Error.Violation ("Renaming of tree node expects matching pattern with tree node\np = " ^ Print.Apx.print_pat p ^"\nq = " ^ print_pat q))

and rename_syn (q : syn_pat) (p : Apx.pat) : (name * name) list =
  match q, p with
  | PBVar _, Apx.PBVar _ -> []
  | PPar n, Apx.PPar m -> [n, m]
  | PLam (es, q), Apx.PLam (sl, p) -> rename_syn q p
  | PSConst (_, qs), Apx.PConst (_, ps) -> rename_all_syn qs ps
  | PUnbox (n, _, _), Apx.PVar m -> [n, m]
  | SInacc _, Apx.Inacc _ -> []
  | PEmpty, Apx.PEmpty -> []
  | PShift _, Apx.PShift _ -> []
  | PDot(sq, q), Apx.PDot (sp, p) -> rename_syn sq sp @ rename_syn q p
  | PUnbox(n, s, cP), Apx.PClos(m, s') -> [n, m]
  | PUnbox(n, s, cP), Apx.Inacc(Apx.Var m) -> [n, m]
  | SInacc (e, s, cP), Apx.PVar m ->
     let rec dig = function
       | Var n -> [n, m]
       | TermBox (_, Unbox(e', _, _)) -> dig e'
       | _ -> raise (Error.Violation "Digging failed")
     in
     dig e
  | _ -> raise (Error.Violation ("Renaming of tree node expects matching pattern with tree node\nq = "
                                   ^ print_syn_pat q ^ "\np = " ^ Print.Apx.print_pat p))

and rename_all (qs : pats) (ps : Apx.pats) : (name * name) list = List.concat (List.map2 rename qs ps)

and rename_all_syn (qs : syn_pats) (ps : Apx.pats) : (name * name) list = List.concat (List.map2 rename_syn qs ps)

(* transform a schema part into a stel *)
let impl_to_tel ps = List.map (fun (n, cP, t) -> (Syntax.Implicit, n, Box (cP, t))) ps

let rec impl_to_ctx = function
  | [] -> []
  | (n, cP, t)::ps -> (n, Box(cP, t)) :: impl_to_ctx ps

let simul_subst_in_impl sigma ps =
    List.map (fun (n, cP, e) -> n, simul_subst_on_bctx sigma cP, simul_subst_syn sigma e) ps

let simul_subst_in_expl sigma ps =
    List.map (fun (n, e) -> n, simul_subst_syn sigma e) ps

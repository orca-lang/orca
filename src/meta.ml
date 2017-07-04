(* Meta operations on the AST, like substitutions and free vars *)

open Util
open Name
open Sign
open Print
open Print.Int
open Syntax
open Syntax.Int

let rec fv cG =
  let fv e = fv cG e in
  let rec in_ctx n = function
    | (x, _) :: _ when x = n -> true
    | _ :: cG -> in_ctx n cG
    | [] -> false
  in
  function
  | Set _ -> []
  | Ctx -> []
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
  | SCtx -> []

and fv_ctx cG = function
  | Nil -> []
  | Snoc(cP, _, e) -> fv_ctx cG cP @ fv_syn cG e
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

  | Ctx -> Ctx
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
  | SCtx -> SCtx
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
  | Ctx -> Ctx
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
  | SCtx -> SCtx
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

(* Substitution of regular variables *)

let fv_subst cG sigma = List.concat (List.map (fun (n, e) -> fv cG e -- n) sigma)

let rec subst (x, es : single_subst) (e : exp) :  exp =
  let f e = subst (x, es) e in
  match e with
  | Set n -> Set n
  | Ctx -> Ctx
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

and subst_syn (x, es) e =
  let f e = subst_syn (x, es) e in
  match e with
  | Star -> Star
  | SCtx -> SCtx
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

let unbox_list_of_ctx cP : ctx -> syn_exp list = List.map (fun (x, _) -> Unbox(Var x, id_sub, cP))
let punbox_list_of_ctx cP : ctx -> syn_pat list = List.map (fun (x, _) -> PUnbox(x, pid_sub, cP))

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

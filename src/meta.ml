(* Meta operations on the AST, like substitutions and free vars *)

open Util
open Name
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
  | Star -> []
  | Ctx -> []
  | Pi (tel, t) -> fv_pi cG tel t
  | SPi (tel, e) -> fv_spi cG tel e
  | Box (ctx, e) -> fv ctx @ fv e
  | Fn (xs, e) ->
     List.fold_left (fun vars x -> vars -- x) (fv e) xs
  | Lam (x, e) -> fv e
  | App (e1, es) -> fv e1 @ List.concat (List.map fv es)
  | AppL (e, es) -> fv e @ List.concat (List.map fv es)
  | Const n -> []
  | Dest n -> []
  | Var n when in_ctx n cG -> []
  | Var n -> [n]
  | BVar i -> []
  | Clos (e1, e2) -> fv e1 @ fv e2
  | EmptyS -> []
  | Shift n -> []
  | Comp (e1, e2)
    | Dot (e1, e2) -> fv e1 @ fv e2
  | ShiftS e -> fv e
  | Snoc (g, _, e) -> fv g @ fv e
  | Nil -> []
  | Annot (e1, e2) -> fv e1 @ fv e2
  | Hole _ -> []

and fv_pi cG (tel : tel) (t : exp) = match tel with
  | [] -> fv cG t
  | (_, n, e)::tel -> fv cG e @ (fv_pi cG tel t -- n)

and fv_spi cG (tel : tel) (t : exp) = match tel with
  | [] -> fv cG t
  | (_, n, e)::tel -> fv cG e @ (fv_spi cG tel t)

let rec fv_pat =
  function
  | PVar n -> [n]
  | PPar _ -> []
  | PBVar i -> []
  | Innac e -> []
  | PLam (f, p) -> fv_pat p
  | PConst (n, ps) -> fv_pats ps
  | PClos (n, p) ->  [n]
  | PEmptyS -> []
  | PShift i -> []
  | PDot (p1, p2) -> fv_pat p1 @ fv_pat p2
  | PNil -> []
  | PSnoc (p1, _, p2) -> fv_pat p1 @ fv_pat p2
  | PUnder -> []
  | PWildcard -> []

and fv_pats ps = List.concat(List.map fv_pat ps)

(* Generate fresh names for all the bound variables,
     to keep names unique *)

let refresh (e : exp) : exp =
  let rec refresh (rep : (name * name) list) : exp -> exp =
    let f x = refresh rep x in
    function
    | Set n -> Set n
    | Star -> Star
    | Ctx -> Ctx
    | Pi (tel, t) -> let tel', t' = refresh_tel rep tel t in Pi(tel', t')
    | SPi (tel, t) -> let tel', t' = refresh_stel rep tel t in SPi(tel', t')
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (xs, e) ->
       let xs' = List.map refresh_name xs in
       let extra = List.map2 (fun x y -> x, y) xs xs in
       Fn (xs', refresh (extra @ rep) e)
    | Lam (x, e) ->
       Lam(x, f e)
    | App (e1, es) -> App(f e1, List.map f es)
    | AppL (e1, es) -> AppL(f e1, List.map f es)
    | Const n -> Const n
    | Dest n -> Dest n
    | Var n ->
       (try
          Var (List.assoc n rep)
        with
          Not_found -> Var n)
    | BVar i -> BVar i
    | Clos (e1, e2) -> Clos(f e1, f e2)
    | EmptyS -> EmptyS
    | Shift n -> Shift n
    | Comp (e1, e2) -> Comp (f e1, f e2)
    | ShiftS e -> ShiftS (f e)
    | Dot (e1, e2) -> Dot (f e1, f e2)
    | Snoc (e1, x, e2) -> Snoc (f e1, x, f e2)
    | Nil -> Nil
    | Annot (e1, e2) -> Annot(f e1, f e2)
    | Hole s -> Hole s

  and refresh_tel (rep : (name * name) list) (tel : tel) (t : exp) : tel * exp =
    match tel with
    | [] -> [], refresh rep t
    | (i, n, e) :: tel ->
       let n' = refresh_name n in
       let tel', t' = refresh_tel ((n, n')::rep) tel t in
       ((i, n', refresh rep e)::tel'), t'

  and refresh_stel (rep : (name * name) list) (tel : tel) (t : exp) : tel * exp =
    match tel with
    | [] -> [], refresh rep t
    | (i, n, e) :: tel ->
       let tel', t' = refresh_stel rep tel t in
       ((i, n, refresh rep e)::tel'), t'
  in
  refresh [] e

(* refresh one free variable *)
let rec refresh_free_var (x , y : name * name) (e : exp) : exp =
  let f e = refresh_free_var (x, y) e in
  match e with
  | Set n -> Set n
  | Star -> Star
  | Ctx -> Ctx
  | Pi (tel, t) ->
     let tel', t' = refresh_free_var_tel (x, y) tel t in
     Pi (tel', t')
  | SPi (tel, t) ->
     let tel', t' = refresh_free_var_stel (x, y) tel t in
     SPi (tel', t')
  | Box (ctx, e) -> Box(f ctx, f e)
  | Fn (xs, _) when List.mem x xs -> raise (Error.Violation "Duplicate variable name")
  | Fn (xs, e) -> Fn (xs, f e)
  | Lam (x, e) -> Lam(x, f e)
  | App (e1, es) -> App(f e1, List.map f es)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | Const n -> Const n
  | Dest n -> Dest n
  | Var n when n = x -> Var y
  | Var n -> Var n
  | BVar i -> BVar i
  | Clos (e1, e2) -> Clos(f e1, f e2)
  | EmptyS -> EmptyS
  | Shift n -> Shift n
  | Comp (e1, e2) -> Comp (f e1, f e2)
  | ShiftS e -> ShiftS (f e)
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | Snoc (g, x, e2) -> Snoc(f g, x, f e2)
  | Nil -> Nil
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s
and refresh_free_var_tel (x, y) tel t =
  match tel with
  | [] -> [], refresh_free_var (x, y) t
  | (i, n, e) :: tel when n = x ->  raise (Error.Violation "Duplicate variable name")
  | (i, n, e) :: tel ->
     let tel', t' = refresh_free_var_tel (x, y) tel t in
     (i, n, refresh_free_var (x, y) e) :: tel', t'
and refresh_free_var_stel (x, y) tel t =
  match tel with
  | [] -> [], refresh_free_var (x, y) t
  | (i, n, e) :: tel ->
     let tel', t' = refresh_free_var_stel (x, y) tel t in
     (i, n, refresh_free_var (x, y) e) :: tel', t'


let refresh_free_vars (rep : (name * name) list) e =
  List.fold_left (fun e (y, y') -> refresh_free_var (y, y') e) e rep

(* Substitution of regular variables *)

type single_subst = name * exp
type subst = single_subst list
type single_psubst = name * pat
type psubst = single_psubst list

let fv_subst cG sigma = List.concat (List.map (fun (n, e) -> fv cG e -- n) sigma)

let rec subst (x, es : single_subst) (e : exp) :  exp =
  let f e = subst (x, es) e in
  match e with
  | Set n -> Set n
  | Star -> Star
  | Ctx -> Ctx
  | Pi (tel, t) ->
     let tel', t' = subst_pi (x, es) tel t in
     Pi(tel', t')
  | SPi (tel, t) ->
     let tel', t' = subst_spi (x, es) tel t in
     SPi(tel', t')
  | Box (ctx, e) -> Box(f ctx, f e)
  | Fn (ys, e) ->
     let ys' = List.map refresh_name ys in
     (* the following cannot happen because y' is just fresh *)
     (* if List.mem y' (fv es) then raise (Error.Violation
       "Duplicate variable name would be captured.") ; *)
     let extra = List.map2 (fun x y -> x, y) ys ys' in
     Fn(ys', subst (x, es) (refresh_free_vars extra e))
  | Lam (x, e) -> Lam(x, f e)
  | App (e1, es) -> App(f e1, List.map f es)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | Const n -> Const n
  | Dest n -> Dest n
  | Var n  when x = n -> refresh es
  | Var n -> Var n
  | BVar i -> BVar i
  | Clos (e1, e2) -> Clos(f e1, f e2)
  | EmptyS -> EmptyS
  | Shift n -> Shift n
  | ShiftS e -> ShiftS (f e)
  | Comp (e1, e2) -> Comp (f e1, f e2)
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | Snoc (e1, x, e2) -> Snoc (f e1, x, f e2)
  | Nil -> Nil
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s
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
  | [] -> [], subst (x, es) t
  | (i, n, e) :: tel ->
     let tel', t' = subst_spi (x, es) tel t in
     (i, n, subst (x, es) e) :: tel', t'

let simul_subst sigma e =
  List.fold_left (fun e s -> subst s e) e sigma

let simul_subst_on_tel sigma tel =
  List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

let simul_subst_on_stel sigma tel =
  List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

let rec compose_single_with_subst s = function
  | [] -> []
  | (y, t') :: sigma -> (y, subst s t') :: (compose_single_with_subst s sigma)

let compose_subst sigma delta = List.map (fun (x, t) -> x, simul_subst sigma t) delta

let rec exp_of_pat_subst : pat_subst -> exp = function
  | CShift n -> Shift n
  | CEmpty -> EmptyS
  | CDot (s, i) -> Dot(exp_of_pat_subst s, BVar i)

let rec exp_of_pat : pat -> exp = function
  | PVar n -> Var n
  | PPar n -> Var n           (* MMMMM *)
  | PBVar i -> BVar i
  | Innac e -> e
  | PLam (f, p) -> Lam (f, exp_of_pat p)
  | PConst (n, ps) -> App (Const n, List.map exp_of_pat ps)
  | PClos (n, s) -> Clos (Var n, exp_of_pat_subst s)
  | PEmptyS -> EmptyS
  | PShift i -> Shift i
  | PDot (p1, p2) -> Dot (exp_of_pat p1, exp_of_pat p2)
  | PNil -> Nil
  | PSnoc (p1, x, p2) -> Snoc (exp_of_pat p1, x, exp_of_pat p2)
  | PUnder -> raise (Error.Violation "We'd also be very surprised if this were to happen.")
  | PWildcard -> raise (Error.Violation "We'd also be very surprised if this were to happen.")

let rec psubst ((x, p') as s) (p : pat) :  pat =
  match p with
  | PVar n when n = x -> p'
  | PVar n -> PVar n
  | PPar n when n = x -> p'   (* MMMMM *)
  | PPar n -> PPar n
  | PBVar i -> PBVar i
  | Innac e -> Innac (subst (x, exp_of_pat p') e)
  | PLam (f, p) -> PLam(f, psubst s p)
  | PConst (n, ps) -> PConst(n, List.map (psubst s) ps)
  | PClos (n, s) when n = x ->
     begin match p' with
     | PVar n' -> PClos (n', s)
     | _ -> assert false (* MMMMMMM *)
     end
  | PClos (n, s) -> PClos (n, s)
  | PEmptyS -> PEmptyS
  | PShift i -> PShift i
  | PDot (p1, p2) -> PDot (psubst s p1, psubst s p2)
  | PNil -> PNil
  | PSnoc (p1, x, p2) -> PSnoc (psubst s p1, x, psubst s p2)
  | PUnder -> PUnder
  | PWildcard -> PWildcard

let rec compose_single_with_psubst s = function
  | [] -> []
  | (y, t') :: sigma -> (y, psubst s t') :: (compose_single_with_psubst s sigma)

let pats_of_psubst : psubst -> pats = List.map snd

let simul_psubst sigma p =
  List.fold_left (fun p s -> psubst s p) p sigma

let simul_psubst_on_list sigma ps =
  List.map (simul_psubst sigma) ps

let compose_psubst sigma delta = List.map (fun (x, t) -> x, simul_psubst sigma t) delta

let exp_list_of_tel tel = List.map (fun (_, _, s) -> s) tel

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

and fv_spi cG (tel : stel) (t : exp) = match tel with
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

  and refresh_stel (rep : (name * name) list) (tel : stel) (t : exp) : stel * exp =
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

let exp_list_of_tel tel = List.map (fun (_, _, s) -> s) tel

let rec exp_of_pat_subst : pat_subst -> exp = function
  | CShift n -> Shift n
  | CEmpty -> EmptyS
  | CDot (s, i) -> Dot(exp_of_pat_subst s, BVar i)

let rec exp_of_pat sign : pat -> exp = function
  | PVar n -> Var n
  | PPar n -> Var n           (* MMMMM *)
  | PBVar i -> BVar i
  | Innac e -> e
  | PLam (fs, p) -> Lam (fs, exp_of_pat sign p)
  | PConst (n, ps) when Sign.is_syn_con sign n ->
     AppL (Const n, List.map (exp_of_pat sign) ps)
  | PConst (n, ps) ->
     App (Const n, List.map (exp_of_pat sign) ps)
  | PClos (n, s) -> Clos (Var n, exp_of_pat_subst s)
  | PEmptyS -> EmptyS
  | PShift i -> Shift i
  | PDot (p1, p2) -> Dot (exp_of_pat sign p1, exp_of_pat sign p2)
  | PNil -> Nil
  | PSnoc (p1, x, p2) -> Snoc (exp_of_pat sign p1, x, exp_of_pat sign p2)
  | PUnder -> raise (Error.Violation "We'd be very surprised if this were to happen.")
  | PWildcard -> raise (Error.Violation "We'd also be very surprised if this were to happen.")

let rec subst_of_pats sign (sigma : pats) (tel : tel) : subst =
  match sigma, tel with
  | [], [] -> []
  | p :: ps, (_, n, t) :: tel' -> (n, exp_of_pat sign p) :: (subst_of_pats sign ps tel')
  | _ -> raise (Error.Violation "subst_of_ctx_map got lists of different lengths")

(* Applying syntactic substitutions *)

let rec syn_subst_stel (sigma : exp) (tel : stel) : stel * exp =
  match tel with
  | [] -> [], sigma
  | (i, n, tt)::tel' ->
     let tel'', sigma' = syn_subst_stel (ShiftS sigma) tel' in
     (i, n, Clos(tt, sigma))::tel'', sigma'

let rec ss_syn_subst_spi (e : exp) (tel : stel) : stel * exp =
  syn_subst_stel (Dot (Shift 1, e)) tel

let rec ss_syn_subst_stel (e : exp) (tel : stel) : stel =
  fst (ss_syn_subst_spi e tel)

let rec syn_subst_spi (sigma : exp) (tel : stel) (t : exp) : stel * exp =
  let tel', sigma' = syn_subst_stel sigma tel in
  tel', Clos(t, sigma')

  let ctx_of_tel : tel -> ctx = List.map (fun (_, x, s) -> x, s)

let exp_list_of_ctx : ctx -> exp list = List.map snd

let subst_of_ctx : ctx -> subst = List.map (fun (x, _) -> x, Var x)

let name_list_of_ctx : ctx -> name list = List.map fst

let var_list_of_ctx : ctx -> exp list = List.map (fun (x, _) -> Var x)

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

open Syntax
open Syntax.Int
open Print.Int
open Meta
open Sign
open Name

type unification_problem
  = Different_constuctors of def_name * def_name
  | Occur_check of name  * exp
  | Expressions_dont_unify of name list * exp * exp
  | Universes_dont_match of int * int
  | Unequal_number_params of  exp list * exp list
  | Unification_didnt_solve_all_problems of exp * exp * ctx * name list * ctx

let print_unification_problem = function
  | Different_constuctors (n, n') ->
     "Constructor " ^ n ^ " and " ^ n' ^ " do not unify."
  | Occur_check (n, e) ->
     "Occurs check failed for " ^ print_name n ^ " in expression " ^ print_exp e ^ "."
  | Expressions_dont_unify (flex, e1, e2) ->
     "Expressions\ne1 = " ^ print_exp e1
     ^ "\ne2 = " ^ print_exp e2
     ^ "\nDo not unify given flexible variable" ^ (if List.length flex > 1 then "s" else "")
     ^ ": " ^ String.concat ", " (List.map print_name flex)
  | Universes_dont_match (n, n') ->
     "Universe " ^ string_of_int n
     ^ " and universe " ^ string_of_int n'
     ^ " do not match."
  | Unequal_number_params (es1, es2) ->
     "Unequal number of params " ^ string_of_int(List.length es1)
     ^ " <> " ^ string_of_int(List.length es1)
     ^ "For expressions\n" ^ print_exps es1
     ^ "\nand\n" ^ print_exps es2
  | Unification_didnt_solve_all_problems (e1, e2, cG, remaining_vars, cG') ->
     "Unification of " ^ print_exp e1 ^ " and " ^ print_exp e2
     ^ " in context " ^ print_ctx cG
     ^ " did not find instances for " ^ print_names remaining_vars
     ^ " which remain free in " ^ print_ctx cG' ^ "."

exception Unification_failure of unification_problem

let rec occur_check sign n e =
  let f e = occur_check sign n e in
  match Whnf.whnf sign e with
  | Var n' -> n = n'
  | Pi (tel, t) -> occur_check_tel sign n tel || occur_check sign n t
  | SPi (tel, t) -> occur_check_stel sign n tel || occur_check sign n t
  | Box (cP, e) -> occur_check_bctx sign n cP || f e
  | Fn (xs, e) when List.mem n xs -> f e
  | Lam (_, e) -> f e
  | Clos (e1, e2, cP) ->
     f e1 || f e2 || occur_check_bctx sign n cP
  | Dot (e1, e2)
    | Annot (e1, e2) -> f e1 || f e2
  | AppL (e, es)
    | App (e, es) ->
     f e || List.fold_left (||) false (List.map (occur_check sign n) es)
  | _ -> false

and occur_check_bctx sign n cP =
  match cP with
  | Nil -> false
  | Snoc (cP, _, e) -> occur_check_bctx sign n cP || occur_check sign n e
  | CtxVar n' -> n = n'

and occur_check_tel sign n tel =
  match tel with
  | [] -> false
  | (_, n', e)::tel when n <> n' ->
     occur_check sign n e || occur_check_tel sign n tel
  | (_, _, e):: _ -> occur_check sign n e
and occur_check_stel sign n tel =
  match tel with
  | [] -> false
  | (_, _, e):: _ ->  occur_check sign n e

let rem n cG = let cG' = List.filter (fun (x, _) -> x <> n) cG in
               Debug.print ~verbose:true  (fun () -> "Removing " ^ print_name n
                                      ^ " from context " ^ print_ctx cG
                                      ^ " yielding " ^ print_ctx cG'); cG'


let rec unify_flex (sign, cG) flex e1 e2 =
  let unify_flex = unify_flex (sign, cG) flex in
  let unify_many cG e1 e2 = unify_flex_many (sign, cG) flex e1 e2 in
  let unify_pi = unify_flex_pi (sign, cG) flex in
  let unify_spi = unify_flex_spi (sign, cG) flex in
  let is_flex n = List.mem n flex in
  let e1', e2' =  Whnf.whnf sign e1, Whnf.whnf sign e2 in
  Debug.print ~verbose:true (fun () -> "Unifying expressions\ne1 = " ^ print_exp e1
                        ^ "\ne2 = " ^ print_exp e2 ^ "\ne1' = " ^ print_exp e1' ^ "\ne2' = " ^ print_exp e2');
  match e1', e2' with
  | Set n , Set n' when n = n' -> cG, []
  | Set n, Set n' -> raise (Unification_failure (Universes_dont_match (n, n')))
  | Pi (tel, t), Pi(tel', t') -> unify_pi tel t tel' t'
  | SPi (tel, t), SPi(tel', t') -> unify_spi tel t tel' t'
  | Box(cP, e), Box(cP', e') ->
     let cG', sigma = unify_flex_bctx (sign, cG) flex cP cP' in
     let cG'', sigma' = unify_flex (simul_subst sigma e) (simul_subst sigma e') in
     cG'', sigma' @ sigma
  | TermBox(cP, e), Box(cP', e') ->
     let cG', sigma = unify_flex_bctx (sign, cG) flex cP cP' in
     let cG'', sigma' = unify_flex (simul_subst sigma e) (simul_subst sigma e') in
     cG'', sigma' @ sigma
  | Fn(ns, e), Fn(ns', e') ->
     let sigma = List.map2 (fun n n' -> (n, Var n')) ns ns' in
     unify_flex (simul_subst sigma e) (simul_subst sigma e')
  | Lam(_,e), Lam(_, e') -> unify_flex e e'
  | App(e, es1), App(e', es2) -> unify_many cG (e::es1) (e'::es2)
  | AppL(e1, es), AppL(e1', es') -> unify_many cG (e1::es) (e1'::es')
  | Const n, Const n' ->
     if n = n' then
       cG, []
     else
       raise (Unification_failure (Different_constuctors (n, n')))

  | Var n, Var n' when n = n' -> cG, []

  | Var n, _ when is_flex n ->
     if not (occur_check sign n e2) then
       ctx_subst (n, e2) (rem n cG), [n, e2]
     else
       raise (Unification_failure (Occur_check (n, e2)))
  | _, Var n when is_flex n ->
     if not (occur_check sign n e1) then
       ctx_subst (n, e1) (rem n cG), [n,e1]
     else
       raise (Unification_failure (Occur_check (n, e1)))
  | BVar i, BVar i' when i = i' -> cG, []
  | Clos(Var n, s1, cP1), Clos(Var m, s2, cP2) when n = m ->
     let _ = try unify_flex_bctx (sign, cG) flex cP1 cP2
             with Unification_failure e -> raise (Error.Violation ("Une petite robe noire"))
     in
     unify_flex s1 s2
  | Clos(Var n, s1, cP1), Clos(Var m, s2, cP2) when is_flex n -> assert false
  | Clos(Var n, s1, cP1), Clos(Var m, s2, cP2) when is_flex m -> assert false
  | Clos(e1, e2, _), Clos(e1', e2', _) ->
     Debug.print ~verbose:true  (fun () -> "e1 = " ^ print_exp e1 ^ "\ne2 = " ^ print_exp e2
                            ^ "\ne1' = " ^ print_exp e1' ^ "\ne2' = " ^ print_exp e2');
     (* unify_many cG [e1;e2] [e1';e2'] *) assert false
  | Empty, Empty -> cG, []
  | Shift n, Shift n' -> cG, []
  | Dot(e1, e2), Dot(e1', e2') -> unify_many cG [e1;e2] [e1';e2']
  | Comp (e1, cP, e2), Comp(e1', cP', e2') -> (* unify_many cG [e1;e2] [e1';e2'] *) assert false
  | Annot(e1, e2), Annot(e1', e2') -> unify_many cG [e1;e2] [e1';e2']
  | Ctx, Ctx -> cG, []
  | BCtx cP, BCtx cP' -> unify_flex_bctx (sign, cG) flex cP cP'
  | _, _ ->
     raise (Unification_failure(Expressions_dont_unify (flex, e1', e2')))

and unify_flex_bctx (sign, cG) flex cP1 cP2 =
  let is_flex n = List.mem n flex in
  match cP1, cP2 with
  | Nil, Nil -> cG, []
  | Snoc(cP1', _, t1), Snoc(cP2', _, t2) ->
     let cG', sigma = unify_flex_bctx (sign, cG) flex cP1' cP2' in
     let cG'', sigma' = unify_flex (sign, cG') flex (simul_subst sigma t1)(simul_subst sigma t2) in
     cG'', sigma' @ sigma

  | CtxVar n, CtxVar n' when n = n' -> cG, []
  | CtxVar n, _ when is_flex n ->
     if not (occur_check_bctx sign n cP2) then
       ctx_subst (n, BCtx cP2) (rem n cG), [n, BCtx cP2]
     else
       raise (Unification_failure (Occur_check (n, BCtx cP2)))
  | _, CtxVar n when is_flex n ->
     if not (occur_check_bctx sign n cP1) then
       ctx_subst (n, BCtx cP1) (rem n cG), [n, BCtx cP1]
     else
       raise (Unification_failure (Occur_check (n, BCtx cP1)))

  | _ -> raise (Unification_failure (Expressions_dont_unify (flex, BCtx cP1, BCtx cP2)))

and unify_flex_many (sign, cG) flex es1 es2 =
  let unify_each (cD, sigma1) e1 e2 =
    let cD', sigma' = unify_flex (sign, cD) flex (simul_subst sigma1 e1) (simul_subst sigma1 e2) in
    cD', sigma' @ sigma1
  in
  if List.length es1 = List.length es2
  then
    List.fold_left2 unify_each (cG, []) es1 es2
  else raise (Unification_failure (Unequal_number_params (es1, es2)))

and unify_flex_pi (sign, cG as ctxs: signature * ctx) (flex : name list) (tel1 : tel) (t1 : exp) (tel2 : tel) (t2 : exp) =
  let simul_subst_in_tel sigma tel =
    List.map (fun (i, n, e) -> i, n, simul_subst sigma e) tel
  in
  match tel1, tel2 with
  | [], [] -> unify_flex ctxs flex t1 t2
  | tel1, [] -> unify_flex ctxs flex (Pi (tel1, t1)) t2
  | [], tel2 -> unify_flex ctxs flex t1 (Pi (tel2, t2))
  | (_, n1, e1)::tel1, (_, n2, e2)::tel2 ->
     let cD, sigma' = unify_flex ctxs flex e1 e2 in
     let sigma = (n1, Var n2) :: sigma'  in
     let tel1' = simul_subst_in_tel sigma tel1 in
     let tel2' = simul_subst_in_tel sigma tel2 in
     let cD', sigma'' = (unify_flex_pi (sign, (n2, e2) :: cD) flex tel1' t1 tel2' t2) in
     cD', sigma @ sigma''

and unify_flex_spi (sign, cG as ctxs: signature * ctx) (flex : name list) (tel1 : stel) (t1 : exp) (tel2 : stel) (t2 : exp) =
  let simul_subst_in_tel sigma tel =
    List.map (fun (i, n, e) -> i, n, simul_subst sigma e) tel
  in
  match tel1, tel2 with
  | [], [] -> unify_flex ctxs flex t1 t2
  | tel1, [] -> unify_flex ctxs flex (SPi (tel1, t1)) t2
  | [], tel2 -> unify_flex ctxs flex t1 (SPi (tel2, t2))
  | (_, n1, e1)::tel1, (_, n2, e2)::tel2 ->
     let cD, sigma' = unify_flex ctxs flex e1 e2 in
     let tel1' = simul_subst_in_tel sigma' tel1 in
     let tel2' = simul_subst_in_tel sigma' tel2 in
     let cD', sigma'' = (unify_flex_spi (sign, cD) flex tel1' t1 tel2' t2) in
     cD', sigma' @ sigma''

let get_flex_vars cG e1 e2 = Util.unique (fv cG e1 @ fv cG e2)
let get_flex_vars_bctx cG e1 e2 = Util.unique (fv_ctx cG e1 @ fv_ctx cG e2)

let unify (sign, cG) e1 e2 =
  let flex_vars = get_flex_vars cG e1 e2 in
  Debug.print ~verbose:true (fun () -> "Flexible unify\ne1 = " ^ print_exp e1
                        ^ "\ne2 = " ^ print_exp e2
                        ^ "\nwith flexible variables= " ^ print_names flex_vars
                        ^ "\nin context Γ = " ^ print_ctx cG
                        ^ ".");
  let cG', sigma = unify_flex (sign, cG) flex_vars e1 e2 in
  let remaining_vars = fv_subst cG' sigma in
  if remaining_vars = []
  then cG', sigma
  else
    raise (Unification_failure(Unification_didnt_solve_all_problems(e1, e2, cG, remaining_vars, cG')))

let unify_many (sign, cG) es1 es2 =
  let flex = List.fold_left2 (fun ns e e' -> ns @ get_flex_vars cG e e') [] es1 es2 in
  let res = unify_flex_many (sign, cG) flex es1 es2 in
  res

let unify_bctx (sign, cG) cP1 cP2 =
  let flex = get_flex_vars_bctx cG cP1 cP2 in
  let res = unify_flex_bctx (sign, cG) flex cP1 cP2 in
  res

let unify_flex (sign, cG) flex e1 e2 =
  let res = unify_flex (sign, cG) flex e1 e2 in
  res

let unify_flex_many (sign, cG) flex es1 es2 =
  let res = unify_flex_many (sign, cG) flex es1 es2 in
  res

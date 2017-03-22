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
  | Box (g, e) -> f g || f e
  | Fn (xs, e) when List.mem n xs -> f e
  | Lam (_, e) -> f e
  | Clos (e1, e2)
  | Snoc (e1, _, e2)
  | Dot (e1, e2)
  | Annot (e1, e2) -> f e1 || f e2
  | AppL (e, es)
  | App (e, es) ->
     f e || List.fold_left (||) false (List.map (occur_check sign n) es)
  | _ -> false
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

let print_subst sigma = "[" ^ String.concat ", " (List.map (fun (x, e) -> print_exp e ^ "/" ^ print_name x) sigma) ^ "]"

type ctx_weakening
  = NoWeakeaning
  | LeftWeakening of int
  | RightWeakening of int

(* cG is context to make types work, cD is initial context and is the
   one we remove unified variables from for the purpose of pattern matching *)
let rec unify_flex (sign, cG) cD flex e1 e2 t =
  let rem n cG = let cG' = List.filter (fun (x, _) -> x <> n) cG in
                 Debug.print (fun () -> "Removing " ^ print_name n ^ " from context " ^ print_ctx cG ^ " yielding " ^ print_ctx cG'); cG' in
  let unify_flex cG = unify_flex (sign, cG) cD flex in
  let unify_many cG e1 e2 = unify_flex_many (sign, cG) cD flex e1 e2 in
  let unify_pi = unify_flex_pi (sign, cG) cD flex in
  let unify_spi = unify_flex_spi (sign, cG) cD flex in
  let is_flex n = List.mem n flex in
  let e1', e2', t =  Whnf.whnf sign e1, Whnf.whnf sign e2, Whnf.whnf sign t in
  Debug.print(fun () -> "Unifying expressions\ne1 = " ^ print_exp e1
    ^ "\ne2 = " ^ print_exp e2 ^ "\ne1' = " ^ print_exp e1' ^ "\ne2' = " ^ print_exp e2');
    match e1', e2', t with
      | Set n , Set n', _ when n = n' -> cD, []
      | Set n, Set n', _ -> raise (Unification_failure (Universes_dont_match (n, n')))
      | Pi (tel, t), Pi(tel', t'), s -> unify_pi tel t tel' t' s
      | SPi (tel, t), SPi(tel', t'), s -> unify_spi tel t tel' t' s
      | Box(g, e), Box(g', e'), s -> unify_many cG [g; e] [g'; e'] [Ctx; s]
      | Fn(ns, e), Fn(ns', e'), Pi(tel, t) ->
         let sigma = List.map2 (fun n n' -> n, Var n') ns ns' in
         let sigma0 = List.map2 (fun (_, n, _) n' -> n, Var n') tel ns' in
         let cG' = (List.map2 (fun (_, _, t) n -> n, t) tel ns') @ cG in
         unify_flex cG' (simul_subst sigma e) (simul_subst sigma e') (simul_subst sigma0 t)
      | Lam(_,e), Lam(_, e'), SPi(tel, t) -> unify_flex cG e e' t
      | App(e1, es1), App(e2, es2), _ -> unify_heads (sign, cG) cD flex e1 e2 es1 es2
      | AppL(e1, es), AppL(e1', es'), _ -> unify_many cG (e1::es) (e1'::es')
      | Const n, Const n', _ ->
         if n = n' then
           cG, []
         else
           raise (Unification_failure (Different_constuctors (n, n')))

      | Var n, Var n', _ when n = n' -> cD, []

      | Var n, _, _ when is_flex n ->
         if not (occur_check sign n e2) then
           ctx_subst (n, e2) (rem n cD), [n, e2]
         else
           raise (Unification_failure (Occur_check (n, e2)))
      | _, Var n, _ when is_flex n ->
         if not (occur_check sign n e1) then
           ctx_subst (n, e1) (rem n cD), [n, e1]
         else
           raise (Unification_failure (Occur_check (n, e1)))
      | BVar i, BVar i', _ when i = i' -> cD, []
      | Clos(e1, e2), Clos(e1', e2'), _ -> unify_many cG [e1;e2] [e1';e2']
      | EmptyS, EmptyS, _ -> cD, []
      | Shift n, Shift n', _ -> cD, [] (* TODO new unification on contexts allowing weakening *)
      | Dot(e1, e2), Dot(e1', e2'), _ -> unify_many cG [e1;e2] [e1';e2']
      | Comp (e1, e2), Comp(e1', e2'), _ -> unify_many cG [e1;e2] [e1';e2']

      | Snoc(e1, _, e2), Snoc(e1', _, e2'), Ctx -> unify_many cG [e1;e2] [e1';e2'] [Ctx; Set 0]
      | Nil, Nil, Ctx -> cD, []

      | Annot(e1, e2), Annot(e1', e2'), s -> unify_many cG [e1;e2] [e1';e2']
      | Ctx, Ctx, Set 0 -> cD, []
      | _ ->
         raise (Unification_failure(Expressions_dont_unify (flex, e1', e2')))

and unify_heads (sign, cG) cD flex e1 e2 es1 es2 =
  let is_flex n = List.mem n flex in
  let unify_many cG e1 e2 = unify_flex_many (sign, cG) cD flex e1 e2 in
  let lookup x s = match lookup_ctx cG x, s with
    | Some (Pi (tel, _)), Some sigma -> List.map (fun (_, _, t) -> subst sigma t) tel
    | Some (Pi (tel, _)), None -> List.map (fun (_, _, t) -> t) tel
    | Some _, _ -> raise (Error.Violation "You promised it was well typed")
    | None, _ -> assert false
  in
  let rem n cG = List.filter (fun (x, _) -> x <> n) cG in
  match e1, e2 with
  | Var x, Var y when is_flex x && is_flex y ->
     raise (Error.Violation "How did we even get here?")
  | Var x, Var y when x = y ->
     unify_many cG es1 es2 (lookup x None)
  | Var x, Var y when is_flex x ->
        unify_many (ctx_subst (x, Var y) (rem x cG)) es1 es2 (lookup y (Some (x, Var y)))
  | Var x, Var y when is_flex y ->
        unify_many (ctx_subst (y, Var x) (rem y cG)) es1 es2 (lookup x (Some (y, Var x)))

  | _ -> assert false

  and unify_flex_many (sign, cG) cD flex es1 es2 ts =
    let unify_each (cG', sigma1) e1 e2 t =
      let cD', sigma' = unify_flex (sign, cG') cD flex (simul_subst sigma1 e1) (simul_subst sigma1 e2) t in
      cD', sigma' @ sigma1
    in
    let rec unify_all (cD', sigma) es1 es2 ts =
      match es1, es2, ts with
      | [], [], [] -> cD', sigma
      | e1::es1, e2::es2, t::ts ->
         let cD'', sigma' = unify_each (cD', sigma) e1 e2 t in
         unify_all (cD'', sigma') es1 es2 ts
      | _ -> raise (Unification_failure (Unequal_number_params (es1, es2)))
    in

     unify_all (cG, []) es1 es2 ts


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

let unify (sign, cG) e1 e2 =
  let flex_vars = get_flex_vars cG e1 e2 in
  Debug.begin_verbose ();
  Debug.print(fun () -> "Flexible unify\ne1 = " ^ print_exp e1
                        ^ "\ne2 = " ^ print_exp e2
                        ^ "\nwith flexible variables= " ^ print_names flex_vars
                        ^ "\nin context Γ = " ^ print_ctx cG
                        ^ ".");
  let cG', sigma = unify_flex (sign, cG) flex_vars e1 e2 in
  Debug.end_verbose ();
  let remaining_vars = fv_subst cG' sigma in
  if remaining_vars = []
  then cG', sigma
  else
    raise (Unification_failure(Unification_didnt_solve_all_problems(e1, e2, cG, remaining_vars, cG')))

let unify_many (sign, cG) es1 es2 =
  let flex = List.fold_left2 (fun ns e e' -> ns @ get_flex_vars cG e e') [] es1 es2 in
  unify_flex_many sign flex es1 es2

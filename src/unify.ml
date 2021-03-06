open Syntax
open Syntax.Int
open Print.Int
open Meta
open Sign
open Name
open Pp

type unification_problem
  = Different_constuctors of def_name * def_name
  | Occur_check of name  * exp
  | Occur_check_syn of name  * syn_exp
  | Expressions_dont_unify of name list * exp * exp
  | Expressions_dont_unify_syn of name list * syn_exp * syn_exp
  | Schemata_dont_unify of name list * schema * schema
  | Schema_expl_dont_unify of name list * schema_part * schema_part (* this may not be necessary until we have implicit schema block members *)
  | Universes_dont_match of int * int
  | Unequal_number_params of exp list * exp list
  | Unequal_number_params_syn of syn_exp list * syn_exp list
  | Unification_didnt_solve_all_problems of exp * exp * ctx * name list * ctx
  | Unification_didnt_solve_all_syn_problems of syn_exp * syn_exp * ctx * name list * ctx

let print_unification_problem =
  let print_flexible_variables flex =
    let len = List.length flex in
    let vars = String.concat ", " (List.map print_name flex) in
    if len = 0 then "Do not unify (there are no flexible variables)"
    else if len = 1 then "Do not unify given flexible variable :" ^ vars
    else "Do not unify given flexible variables :" ^ vars
  in

  function
  | Different_constuctors (n, n') ->
     "Constructor " ^ n ^ " and " ^ n' ^ " do not unify.\n"
  | Occur_check (n, e) ->
     "Occurs check failed for " ^ print_name n ^ " in expression " ^ print_exp e ^ ".\n"
  | Occur_check_syn (n, e) ->
     "Occurs check failed for " ^ print_name n ^ " in expression " ^ print_syn_exp e ^ ".\n"
  | Schemata_dont_unify (flex, sch1, sch2) ->
     "Schemata do not unify.\n"
  | Schema_expl_dont_unify (flex, _, _) ->
     "Schema parts do not unify.\n"
  | Expressions_dont_unify (flex, e1, e2) ->
     "Expressions\ne1 = " ^ print_exp e1
     ^ "\ne2 = " ^ print_exp e2
     ^ "\n" ^ print_flexible_variables flex
  | Expressions_dont_unify_syn (flex, e1, e2) ->
     "Expressions\ne1 = " ^ print_syn_exp e1
     ^ "\ne2 = " ^ print_syn_exp e2
     ^ "\n" ^ print_flexible_variables flex

  | Universes_dont_match (n, n') ->
     "Universe " ^ string_of_int n
     ^ " and universe " ^ string_of_int n'
     ^ " do not match."
  | Unequal_number_params (es1, es2) ->
     "Unequal number of params " ^ string_of_int(List.length es1)
     ^ " <> " ^ string_of_int(List.length es2)
     ^ "\nFor expressions\n" ^ print_exps es1
     ^ "\nand\n" ^ print_exps es2
  | Unequal_number_params_syn (es1, es2) ->
     "Unequal number of params " ^ string_of_int(List.length es1)
     ^ " <> " ^ string_of_int(List.length es2)
     ^ "\nFor syntactic expressions\n" ^ print_syn_exps es1
     ^ "\nand\n" ^ print_syn_exps es2
  | Unification_didnt_solve_all_problems (e1, e2, cG, remaining_vars, cG') ->
     "Unification of " ^ print_exp e1 ^ " and " ^ print_exp e2
     ^ " in context " ^ print_ctx cG
     ^ " did not find instances for " ^ print_names remaining_vars
     ^ " which remain free in " ^ print_ctx cG' ^ "."
  | Unification_didnt_solve_all_syn_problems (e1, e2, cG, remaining_vars, cG') ->
     "Unification of " ^ print_syn_exp e1 ^ " and " ^ print_syn_exp e2
     ^ " in context " ^ print_ctx cG
     ^ " did not find instances for " ^ print_names remaining_vars
     ^ " which remain free in " ^ print_ctx cG' ^ "."


exception Unification_failure of unification_problem

(* Register the printer, if the exception is not catched, get some default error message *)
let () =
  Printexc.register_printer
    (function
      | Unification_failure problem -> Some (Printf.sprintf "Unification failure (%s)" (print_unification_problem problem))
      | _ -> None (* for other exceptions *)
    )

let rec occur_check sign n e =
  let f e = occur_check sign n e in
  match Whnf.whnf sign e with
  | Var n' -> n = n'
  | Pi (tel, t) -> occur_check_tel sign n tel || f t
  | Box (cP, e) -> occur_check_bctx sign n cP || occur_check_syn sign cP n e
  | TermBox (cP, e) -> occur_check_bctx sign n cP || occur_check_syn sign cP n e
  | Fn (xs, e) when not (List.mem n xs) -> f e
  | Annot (e1, e2) -> f e1 || f e2
  | App (e, es) ->
     f e || List.fold_left (||) false (List.map (occur_check sign n) es)
  | BCtx cP -> occur_check_bctx sign n cP
  | Hole _ -> false
  | _ -> false

and occur_check_syn sign cP n e =
  let f cP e = occur_check_syn sign cP n e in
  match Whnf.rewrite sign cP e with
  | SPi (tel, t) -> occur_check_stel sign cP n tel || f cP t
  | AppL (e, es) -> f cP e || List.fold_left (||) false (List.map (f cP) es)
  | Lam (xs, e) -> f (bctx_of_lam_pars cP xs) e
  | Dot (e1, e2) -> f cP e1 || f cP e2
  | SBCtx cP -> occur_check_bctx sign n cP
  | Unbox (e, s) -> f cP s || occur_check sign n e
  | _ -> false


and occur_check_bctx sign n cP =
  match cP with
  | Nil -> false
  | Snoc (cP, _, e) -> occur_check_bctx sign n cP || occur_check_syn sign cP n e
  | CtxVar n' -> n = n'

and occur_check_tel sign n tel =
  match tel with
  | [] -> false
  | (_, n', e)::tel when n <> n' ->
     occur_check sign n e || occur_check_tel sign n tel
  | (_, _, e):: _ -> occur_check sign n e
and occur_check_stel sign cP n tel =
  match tel with
  | [] -> false
  | (_, x, e):: tel -> occur_check_syn sign cP n e || occur_check_stel sign (Snoc (cP, x, e)) n tel

let rem n cG = let cG' = List.filter (fun (x, _) -> x <> n) cG in
               Debug.print ~verbose:true  (fun () -> "Removing " ^ print_name n
                                      ^ " from context " ^ print_ctx cG
                                      ^ "\nyielding " ^ print_ctx cG'); cG'

let rec unify_flex (sign, cG) flex e1 e2 =
  let unify_flex = unify_flex (sign, cG) flex in
  let unify_many cG e1 e2 = unify_flex_many (sign, cG) flex e1 e2 in
  let unify_pi = unify_flex_pi (sign, cG) flex in
  let is_flex n = List.mem n flex in
  let e1', e2' =  Whnf.normalize sign e1, Whnf.normalize sign e2 in
  Debug.print ~verbose:true (fun () -> "Unifying expressions\ne1 = " ^ Pretty.print_exp cG e1
    ^ "\ne2 = " ^ Pretty.print_exp cG e2 ^ "\ne1' = " ^ Pretty.print_exp cG e1'
    ^ "\ne2' = " ^ Pretty.print_exp cG e2');
  match e1', e2' with
  | Set n , Set n' when n = n' -> cG, []
  | Set n, Set n' -> raise (Unification_failure (Universes_dont_match (n, n')))
  | Pi (tel, t), Pi(tel', t') -> unify_pi tel t tel' t'
  | Box(cP, e), Box(cP', e') ->
     let cG', sigma = unify_flex_bctx (sign, cG) flex cP cP' in
     let cG'', sigma' = unify_flex_syn (sign, cG) cP flex (simul_subst_syn sigma e) (simul_subst_syn sigma e') in
     cG'', sigma' @ sigma
  | TermBox(cP, e), TermBox(cP', e') ->
     let cG', sigma = unify_flex_bctx (sign, cG) flex cP cP' in
     let cG'', sigma' = unify_flex_syn (sign, cG) cP flex (simul_subst_syn sigma e) (simul_subst_syn sigma e') in
     cG'', sigma' @ sigma
  | Fn(ns, e), Fn(ns', e') ->
     let sigma = List.map2 (fun n n' -> (n, Var n')) ns ns' in
     unify_flex (simul_subst sigma e) (simul_subst sigma e')
  | App(e, es1), App(e', es2) -> unify_many cG (e::es1) (e'::es2)
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
  | Annot(e1, e2), Annot(e1', e2') -> unify_many cG [e1;e2] [e1';e2']
  | Ctx sch , Ctx sch' ->  unify_flex_schemata (sign, cG) flex sch sch'
  | BCtx cP, BCtx cP' -> unify_flex_bctx (sign, cG) flex cP cP'
  | _, Hole _
  | Hole _, _ -> cG, []
  | _, _ ->
     raise (Unification_failure(Expressions_dont_unify (flex, e1', e2')))

and unify_flex_schemata (sign, cG) flex (Schema (quant1, block1)) (Schema (quant2, block2)) =
  let cD, sigma = unify_flex_schema_expl (sign, cG) Nil flex quant1 quant2 in 
  let cP' = bctx_of_quant Nil (simul_subst_in_part sigma quant1) in 
  unify_flex_schema_expl (sign, cG) cP' flex block1 block2

and unify_flex_schema_expl (sign, cG: signature * ctx) cP (flex : name list) (ps1: schema_part)  (ps2 : schema_part) =
  let simul_subst_in_part sigma ps =
    List.map (fun (n, e) -> n, simul_subst_syn sigma e) ps
  in
  match ps1, ps2 with
  | [], [] ->  cG, []
  | _, []
  | [], _ -> raise (Unification_failure (Schema_expl_dont_unify (flex, ps1, ps2)))
  | (n1, e1)::ps1, (n2, e2)::ps2 ->
     let cD, sigma' = unify_flex_syn (sign, cG) cP flex e1 e2 in
     let ps1' = simul_subst_in_part sigma' ps1 in
     let ps2' = simul_subst_in_part sigma' ps2 in
     let cD', sigma'' = (unify_flex_schema_expl (sign, cD) (Snoc (cP, n1, simul_subst_syn sigma' e1)) flex ps1' ps2') in
     cD', sigma' @ sigma''

and unify_flex_syn (sign, cG) cP flex e1 e2 =
  let is_flex n = List.mem n flex in
  let unify_spi = unify_flex_spi (sign, cG) cP flex in
  let unify_many_syn e1 e2 = unify_flex_many_syn (sign, cG) cP flex e1 e2 in
  let e1', e2' =  Whnf.normalize_syn sign cP e1, Whnf.normalize_syn sign cP e2 in
  Debug.print ~verbose:true (fun () -> "Unifying syntactic expressions in context " ^ print_ctx (Whnf.whnf_ctx sign cG)
    ^ "\ncP = " ^ print_bctx cP
    ^ "\ne1 = " ^ print_syn_exp e1 ^ "\ne2 = " ^ print_syn_exp e2
    ^ "\ne1' = " ^ print_syn_exp e1'
    ^ "\ne2' = " ^ print_syn_exp e2');
  match e1', e2' with
  | SPi (tel, t), SPi(tel', t') -> unify_spi tel t tel' t'
  | Lam(_,e), Lam(xs, e') -> unify_flex_syn (sign, cG) (bctx_of_lam_pars cP xs) flex e e'
  | AppL(e1, es), AppL(e1', es') -> unify_many_syn (e1::es) (e1'::es')
  | BVar i, BVar i' when i = i' -> cG, []
  | Empty, Empty -> cG, []
  | Shift n, Shift n' when n = n' -> cG, []
  | Shift 0, Empty when cP = Nil -> cG, []
  | Empty, Shift 0 when cP = Nil -> cG, []
  | Dot(e1, e2), Dot(e1', e2') -> unify_many_syn [e1;e2] [e1';e2']
  | SCtx sch, SCtx sch' -> unify_flex_schemata (sign, cG) flex sch sch'
  | SBCtx cP, SBCtx cP' -> unify_flex_bctx (sign, cG) flex cP cP'
  | Star, Star -> cG, []
  (* This is comparing eta long and eta short versions *)
  | Unbox(Var n, s), Lam (xs, (AppL (Unbox (Var m, s'), es))) when n = m ->
    Debug.print (fun () -> "Hello!");
    let n = List.length xs in
    let rec is_eta n =
      function
      | BVar m :: es when n = m -> is_eta (dec_idx n) es
      | [] -> true
      | _ -> false
    in
    if is_eta (n-1, None) es then
      unify_flex_syn (sign, cG) cP flex s' (weaken_syn n s)
    else
      raise (Unification_failure(Expressions_dont_unify_syn (flex, e1', e2')))
  | Lam (xs, (AppL (Unbox (Var m, s'), es))), Unbox(Var n, s) when n = m  ->
    let n = List.length xs in
    let rec is_eta n =
      function
      | BVar m :: es when n = m -> is_eta (dec_idx n) es
      | [] -> true
      | _ -> false
    in
    if is_eta (n-1, None) es then
      unify_flex_syn (sign, cG) cP flex s' (weaken_syn n s)
    else
      raise (Unification_failure(Expressions_dont_unify_syn (flex, e1', e2')))

  | Unbox(Var n, Empty), Unbox (Var m, Shift 0) (* when n = m -> cG, [] *)
  | Unbox(Var n, Shift 0), Unbox (Var m, Empty) when n = m -> cG, []
  | Unbox(Var n, s), Unbox (Var m, s') when n = m ->  unify_flex_syn (sign, cG) cP flex s s'
  | Unbox(Var n, s), _ when is_flex n ->
    Debug.print (fun () -> "Unifying variable " ^ print_name n ^ " which is flexible");
     if not (occur_check_syn sign cP n e2') then
       try
        Debug.print (fun () -> "Inverse substitution is computed in ctx " ^ print_bctx cP);
         match apply_inv_subst e2' s with
         | None -> raise (Unification_failure (Expressions_dont_unify_syn(flex, e1', e2')))
         | Some e ->
            let cP' = apply_inv_subst_ctx cP s in
            let e' = Whnf.whnf sign (TermBox (cP', e)) in
            ctx_subst (n, e') (rem n cG), [n, e']
       with
         Inv_fail -> raise (Unification_failure (Expressions_dont_unify_syn(flex, e1', e2')))
     else
       raise (Unification_failure(Occur_check_syn (n, e2)))
  | _, Unbox(Var n, s) when is_flex n ->
  Debug.print (fun () -> "Unifying variable " ^ print_name n ^ " which is flexible");
     if not (occur_check_syn sign cP n e1') then
       try
        Debug.print (fun () -> "Inverse substitution is computed in ctx " ^ print_bctx cP);
         match apply_inv_subst e1' s with
         | None -> raise (Unification_failure (Expressions_dont_unify_syn(flex, e1', e2')))
         | Some e ->
            let cP' = apply_inv_subst_ctx cP s in
            let e' =  Whnf.whnf sign (TermBox (cP', e)) in
            ctx_subst (n, e') (rem n cG), [n, e']
       with
         Inv_fail -> raise (Unification_failure (Expressions_dont_unify_syn(flex, e1', e2')))
     else
       raise (Unification_failure(Occur_check_syn (n, e1)))

  | Unbox(e1, s1), Unbox(e2, s2) ->
     let cG', sigma = unify_flex_syn (sign, cG) cP flex s1 s2 in
     let cG'' = cG' in
     (* let cP1' = simul_subst_on_bctx sigma cP1 in *)
     (* let cG'', sigma' = unify_flex_bctx (sign, cG') flex cP1' (simul_subst_on_bctx sigma cP2) in *)
     let sigma0 = (* sigma' @ *) sigma in
     let cG''', sigma'' = unify_flex (sign, cG'') flex (simul_subst sigma0 e1) (simul_subst sigma0 e2) in
     cG''', sigma'' @ sigma0
  | SConst n, SConst n' ->
     if n = n' then
       cG, []
     else
       raise (Unification_failure (Different_constuctors (n, n')))
  | _, _ ->
     raise (Unification_failure(Expressions_dont_unify_syn (flex, e1', e2')))

and unify_flex_bctx (sign, cG) flex cP1 cP2 =
  let is_flex n = List.mem n flex in
  match cP1, cP2 with
  | Nil, Nil -> cG, []
  | Snoc(cP1', _, t1), Snoc(cP2', _, t2) ->
     let cG', sigma = unify_flex_bctx (sign, cG) flex cP1' cP2' in
     let cG'', sigma' = unify_flex_syn (sign, cG') (simul_subst_on_bctx sigma cP1')
                                        flex (simul_subst_syn sigma t1)(simul_subst_syn sigma t2) in
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

and unify_flex_many_syn (sign, cG) cP flex es1 es2 =
  let unify_each e1 e2 (cD, sigma1) =
    let cD', sigma' = unify_flex_syn (sign, cD) cP flex (simul_subst_syn sigma1 e1) (simul_subst_syn sigma1 e2) in
    cD', sigma' @ sigma1
  in
  if List.length es1 = List.length es2
  then
    List.fold_right2 unify_each es1 es2 (cG, [])
  else raise (Unification_failure (Unequal_number_params_syn (es1, es2)))

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

and unify_flex_spi (sign, cG as ctxs: signature * ctx) cP (flex : name list) (tel1 : stel) (t1 : syn_exp) (tel2 : stel) (t2 : syn_exp) =
  let simul_subst_in_stel sigma tel =
    List.map (fun (i, n, e) -> i, n, simul_subst_syn sigma e) tel
  in
  match tel1, tel2 with
  | [], [] -> unify_flex_syn ctxs cP flex t1 t2
  | tel1, [] -> unify_flex_syn ctxs cP flex (SPi (tel1, t1)) t2
  | [], tel2 -> unify_flex_syn ctxs cP flex t1 (SPi (tel2, t2))
  | (_, n1, e1)::tel1, (_, n2, e2)::tel2 ->
     let cD, sigma' = unify_flex_syn ctxs cP flex e1 e2 in
     let tel1' = simul_subst_in_stel sigma' tel1 in
     let tel2' = simul_subst_in_stel sigma' tel2 in
     let cD', sigma'' = (unify_flex_spi (sign, cD) (Snoc (cP, n1, simul_subst_syn sigma' e1)) flex tel1' t1 tel2' t2) in
     cD', sigma' @ sigma''

let get_flex_vars cG e1 e2 = Util.unique (fv cG e1 @ fv cG e2)
let get_flex_vars_syn cG e1 e2 = Util.unique (fv_syn cG e1 @ fv_syn cG e2)
let get_flex_vars_bctx cG e1 e2 = Util.unique (fv_ctx cG e1 @ fv_ctx cG e2)

let unify_syn (sign, cG) cP e1 e2 =
  let flex_vars = get_flex_vars_syn cG e1 e2 in
  Debug.print ~verbose:true (fun () -> "Flexible unify\ne1 = " ^ print_syn_exp e1
                        ^ "\ne2 = " ^ print_syn_exp e2
                        ^ "\nwith flexible variables= " ^ print_names flex_vars
                        ^ "\nin context Γ = " ^ print_ctx cG
                        ^ ".");
  let cG', sigma = unify_flex_syn (sign, cG) cP flex_vars e1 e2 in
  let remaining_vars = fv_subst cG' sigma in
  if remaining_vars = []
  then cG', sigma
  else
    raise (Unification_failure(Unification_didnt_solve_all_syn_problems(e1, e2, cG, remaining_vars, cG')))

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

let unify_many_syn (sign, cG) cP es1 es2 =
  let flex = List.fold_left2 (fun ns e e' -> ns @ get_flex_vars_syn cG e e') [] es1 es2 in
  let res = unify_flex_many_syn (sign, cG) cP flex es1 es2 in
  res

let unify_bctx (sign, cG) cP1 cP2 =
  let flex = get_flex_vars_bctx cG cP1 cP2 in
  let res = unify_flex_bctx (sign, cG) flex cP1 cP2 in
  res

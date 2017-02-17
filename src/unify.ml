open Syntax.Int

let rec occur_check n e =
  let f e = occur_check n e in
  match e with
  | Var n' -> n = n'
  | Pi (tel, t) -> occur_check_tel n tel || occur_check n t
  | Arr (s , t) -> f s || f t
  | Box (g, e) -> f g || f e
  | Fn (x, e) when x != n -> f e
  | Lam (_, e) -> f e
  | AppL (e1, e2)
  | Clos (e1, e2)
  | Comma (e1, e2)
  | Subst (e1, e2)
  | Annot (e1, e2) -> f e1 || f e2
  | App (e, es) ->
     f e || List.fold_left (||) false (List.map (occur_check n) es)
  | _ -> false
and occur_check_tel n tel =
  match tel with
  | [] -> false
  | Unnamed e::tel -> occur_check n e || occur_check_tel n tel
  | Named (n', e)::tel when n != n' ->
     occur_check n e || occur_check_tel n tel
  | Named (_, e):: _ ->
     occur_check n e

let print_subst sigma = "[" ^ String.concat ", " (List.map (fun (x, e) -> print_exp e ^ "/" ^ print_name x) sigma) ^ "]"

let rec unify sign e1 e2 =
  Debug.print (fun () -> "Comparing: " ^ print_exp e1 ^ " and " ^ print_exp e2) ;
  Debug.indent() ;
  let sigma = match Whnf.whnf sign e1, Whnf.whnf sign e2 with
    | Star, Star -> []
    | Set n , Set n' when n = n' -> []
    | Set n, Set n' -> raise (Error.Error ("Universes don't match: " ^ string_of_int n ^ " != " ^ string_of_int n'))
    (* | Pi(Some n, s, t), Pi(Some n',s',t') -> *)
    (*    let sigma1 = (n, Var n') :: unify sign s s' in *)
    (*    let sigma2 = unify sign (subst_list sigma1 t) (subst_list sigma1 t') in *)
    (*    sigma1 @ sigma2 *)
    (* | Pi(_, s, t), Pi(_, s',t') -> unify2 sign s s' t t' *)
    | Pi (tel, t), _ -> assert false
    | Arr(e1, e2), Arr(e1', e2') -> unify2 sign e1 e1' e2 e2'
    | Box(g, e), Box(g', e') -> unify2 sign g g' e e'
    | Fn(n, e), Fn(n', e') -> (n, Var n') :: unify sign (subst (n, Var n') e) (subst (n, Var n') e')
    | Lam(_,e), Lam(_, e') -> unify sign e e'
    | App(e, es), App(e', es') ->
       unify sign e e' @ unify_many sign es es'
    | AppL(e1, e2), AppL(e1', e2') -> unify2 sign e1 e1' e2 e2'
    | Const n, Const n' ->
       if n = n' then
         []
       else
         raise (Error.Error ("Constructor " ^ n ^ " does not unify with constructor " ^ n' ^ "."))
    | Var n, Var n' ->
       if n = n' then [] else [n , Var n']
    | Var n, _ ->
       if not (occur_check n e2) then
         [n, e2]
       else
         raise (Error.Error ("Occur check failed for " ^ print_name n ^ " in term " ^ print_exp e2 ^ "."))
    | _, Var n ->
       if not (occur_check n e1) then
         [n, e1]
       else
         raise (Error.Error ("Occur check failed for " ^ print_name n ^ " in term " ^ print_exp e1 ^ "."))
    | BVar i, BVar i' -> assert (i = i'); []
    | Clos(e1, e2), Clos(e1', e2') -> unify2 sign e1 e1' e2 e2'
    | EmptyS, EmptyS -> []
    | Shift n, Shift n' -> []
    | Comma(e1, e2), Comma(e1', e2') -> unify2 sign e1 e1' e2 e2'
    | Subst(e1, e2), Subst(e1', e2') -> unify2 sign e1 e1' e2 e2'
    | Nil, Nil -> []
    | Annot(e1, e2), Annot(e1', e2') -> unify2 sign e1 e1' e2 e2'
    | Under, _ -> []
    | _, Under -> []
    | _, _ ->
       raise (Error.Error ("Expression " ^ print_exp e1 ^ " does not unify with " ^ print_exp e2 ^ "."))
  in
  Debug.deindent();
  Debug.print (fun () -> "Resulted in: " ^ print_subst sigma);
  sigma

and unify2 sign e1 e1' e2 e2' =
  let sigma1 = unify sign e1 e1' in
  let sigma2 = unify sign (subst_list sigma1 e2) (subst_list sigma1 e2') in
  sigma1 @ sigma2

and unify_many sign es1 es2 =
  if List.length es1 = List.length es2
  then List.concat (List.map2 (unify sign) es1 es2) (* THIS IS VERY WRONG, you need to apply substitutions *)
  else raise (Error.Error "Unequal number of parameters during unification.")

and unify_tel sign tel1 t1 tel2 t2 =
  match tel1, tel2 with
  | [], [] -> unify sign t1 t2
  | tel1, [] -> assert false    (* if t2 is a variables it unifies with the rest of the telescope *)
  | [], tel2 -> assert false    (* if t1 is a variables it unifies with the rest of the telescope *)
  | Unnamed e1::tel1, Unnamed e2::tel2 -> assert false
  | Unnamed e1::tel1, Named (n2, e2)::tel2 -> assert false
  | Named (n1, e1)::tel1, Named (n, e)::tel -> assert false
  | Named (n1, e1)::tel1, Unnamed e2::tel2 -> assert false

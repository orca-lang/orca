open Syntax.Int
open Name

let rec occur_check n e =
  let f e = occur_check n e in
  match e with
  | Var n' -> n = n'
  | Pi (tel, t) -> occur_check_tel n tel || occur_check n t
  | Arr (s , t) -> f s || f t
  | Box (g, e) -> f g || f e
  | Fn (xs, e) when List.mem n xs -> f e
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
  (* | Unnamed e::tel -> occur_check n e || occur_check_tel n tel *)
  | (_, n', e)::tel when n != n' ->
     occur_check n e || occur_check_tel n tel
  | (_, _, e):: _ ->
     occur_check n e

let print_subst sigma = "[" ^ String.concat ", " (List.map (fun (x, e) -> print_exp e ^ "/" ^ print_name x) sigma) ^ "]"

let rec unify sign e1 e2 =
  Debug.print (fun () -> "Comparing: " ^ print_exp e1 ^ " and " ^ print_exp e2) ;
  Debug.indent() ;
  let sigma = match Whnf.whnf sign e1, Whnf.whnf sign e2 with
    | Univ Star, Univ Star -> []
    | Univ (Set n) , Univ(Set n') when n = n' -> []
    | Univ (Set n), Univ(Set n') -> raise (Error.Error ("Universes don't match: " ^ string_of_int n ^ " != " ^ string_of_int n'))
    | Pi (tel, t), Pi(tel', t') -> unify_tel sign tel t tel' t'
    | Arr(e1, e2), Arr(e1', e2') -> unify_many sign [e1;e2] [e1';e2']
    | Box(g, e), Box(g', e') -> unify_many sign [g; e] [g'; e']
    | Fn(ns, e), Fn(ns', e') ->
       let sigma = List.map2 (fun n n' -> (n, Var n')) ns ns' in
       sigma @ unify sign (subst_list sigma e) (subst_list sigma e')
    | Lam(_,e), Lam(_, e') -> unify sign e e'
    | App(e, es1), App(e', es2) ->
       let sigma = unify sign e e' in
       let es1' = List.map (subst_list sigma) es1 in
       let es2' = List.map (subst_list sigma) es2 in
       unify sign e e' @ unify_many sign es1' es2'
    | AppL(e1, e2), AppL(e1', e2') -> unify_many sign [e1;e2] [e1';e2']
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
    | BVar i, BVar i' when i = i' -> []
    | Clos(e1, e2), Clos(e1', e2') -> unify_many sign [e1;e2] [e1';e2']
    | EmptyS, EmptyS -> []
    | Shift n, Shift n' -> []
    | Comma(e1, e2), Comma(e1', e2') -> unify_many sign [e1;e2] [e1';e2']
    | Subst(e1, e2), Subst(e1', e2') -> unify_many sign [e1;e2] [e1';e2']
    | Nil, Nil -> []
    | Annot(e1, e2), Annot(e1', e2') -> unify_many sign [e1;e2] [e1';e2']
    | Under, _ -> []
    | _, Under -> []
    | _, _ ->
       raise (Error.Error ("Expression " ^ print_exp e1 ^ " does not unify with " ^ print_exp e2 ^ "."))
  in
  Debug.deindent();
  Debug.print (fun () -> "Resulted in: " ^ print_subst sigma);
  sigma

and unify_many sign es1 es2 =
  let unify_each sigma1 e1 e2 =
    sigma1 @ unify sign (subst_list sigma1 e1) (subst_list sigma1 e2)
  in
  if List.length es1 = List.length es2
  then
    List.fold_left2 unify_each [] es1 es2
  else raise (Error.Error "Unequal number of parameters during unification.")

and unify_tel sign tel1 t1 tel2 t2 =
  let subst_list_in_tel sigma tel =
    List.map (fun (i, n, e) -> i, n, subst_list sigma e) tel
  in
  match tel1, tel2 with
  | [], [] -> unify sign t1 t2
  | tel1, [] -> unify sign (Pi (tel1, t1)) t2
  | [], tel2 -> unify sign t1 (Pi (tel2, t2))
  | (_, n1, e1)::tel1, (_, n2, e2)::tel2 ->
     let sigma = (n1, Var n2) :: (unify sign e1 e2) in
     let tel1' = subst_list_in_tel sigma tel1 in
     let tel2' = subst_list_in_tel sigma tel2 in
     sigma @ (unify_tel sign tel1' t1 tel2' t2)

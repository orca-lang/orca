open Syntax.Int

let eq e1 e2 =
  let rec eq alpha e1 e2 =
    match e1, e2 with
    | Star, Star -> true
    | Set n , Set n' when n = n' -> true
    | Set n, Set n' -> raise (Error.Error ("Universes don't match: " ^ string_of_int n ^ " != " ^ string_of_int n'))
    | Pi(Some n, s, t), Pi(Some n',s',t') ->
       eq alpha s s' && eq ((n, n') :: alpha) t t'
    | Pi(_, s, t), Pi(_, s',t') ->
       eq alpha s s' && eq alpha t t'
    | Arr(e1, e2), Arr(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | Box(g, e), Box(g', e') -> eq alpha g g' && eq alpha e e'
    | Fn(n, e), Fn(n', e') -> eq ((n,n'):: alpha) e e'
    | Lam(_,e), Lam(_, e') -> eq alpha e e'
    | App(e1, e2), App(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | AppL(e1, e2), AppL(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | Const n, Const n' -> n = n'
    | Var n, Var n' ->
       begin try
         let newn' = List.assoc n alpha in
         newn' = n'
       with
         Not_found ->
         (* this should rarely happen, but it might when comparing a
            pi type that does not bound a var with one that does *)
         false
       end
    | BVar i, BVar i' -> i = i'
    | Clos(e1, e2), Clos(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | EmptyS, EmptyS -> true
    | Shift n, Shift n' -> n = n'
    | Comma(e1, e2), Comma(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | Subst(e1, e2), Subst(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | Nil, Nil -> true
    | Annot(e1, e2), Annot(e1', e2') -> eq alpha e1 e1' && eq alpha e2 e2'
    | Under, Under -> true

    | _, _ ->
       false
  in
  Debug.print (fun () -> "Comparing: " ^ print_exp e1 ^ " and " ^ print_exp e2) ;
  let res = eq [] e1 e2 in
  Debug.print (fun () -> "Resulted in: " ^ string_of_bool res) ;
  res

let rec occurCheck n e =
  let f e = occurCheck n e in
  match e with
  | Var n' -> n = n'
  | Pi (Some n', s, t) when n != n' -> f s || f t
  | Pi (None, s, t) -> f s || f t
  | Arr (s , t) -> f s || f t
  | Box (g, e) -> f g || f e
  | Fn (x, e) when x != n -> f e
  | Lam (_, e) -> f e
  | App (e1, e2)
  | AppL (e1, e2)
  | Clos (e1, e2)
  | Comma (e1, e2)
  | Subst (e1, e2)
  | Annot (e1, e2) -> f e1 || f e2
  | _ -> false

let print_subst sigma = "[" ^ String.concat ", " (List.map (fun (x, e) -> print_exp e ^ "/" ^ print_name x) sigma) ^ "]"

let rec unify e1 e2 =
  Debug.print (fun () -> "Comparing: " ^ print_exp e1 ^ " and " ^ print_exp e2) ;
  let sigma = match e1, e2 with
    | Star, Star -> []
    | Set n , Set n' when n = n' -> []
    | Set n, Set n' -> raise (Error.Error ("Universes don't match: " ^ string_of_int n ^ " != " ^ string_of_int n'))
    | Pi(Some n, s, t), Pi(Some n',s',t') ->
       let sigma1 = (n, Var n') :: unify s s' in
       let sigma2 = unify (subst_list sigma1 t) (subst_list sigma1 t') in
       sigma1 @ sigma2
    | Pi(_, s, t), Pi(_, s',t') -> unify2 s s' t t'
    | Arr(e1, e2), Arr(e1', e2') -> unify2 e1 e1' e2 e2'
    | Box(g, e), Box(g', e') -> unify2 g g' e e'
    | Fn(n, e), Fn(n', e') -> (n, Var n') :: unify (subst (n, Var n') e) (subst (n, Var n') e')
    | Lam(_,e), Lam(_, e') -> unify e e'
    | App(e1, e2), App(e1', e2') -> unify2 e1 e1' e2 e2'
    | AppL(e1, e2), AppL(e1', e2') -> unify2 e1 e1' e2 e2'
    | Const n, Const n' ->
       if n = n' then
         []
       else
         raise (Error.Error ("Constructor " ^ n ^ " does not unify with constructor " ^ n' ^ "."))
    | Var n, Var n' ->
       if n = n' then [] else [n , Var n']
    | Var n, _ ->
       if not (occurCheck n e2) then
         [n, e2]
       else
         raise (Error.Error ("Occur check failed for " ^ print_name n ^ " in term " ^ print_exp e2 ^ "."))
    | _, Var n ->
       if not (occurCheck n e1) then
         [n, e1]
       else
         raise (Error.Error ("Occur check failed for " ^ print_name n ^ " in term " ^ print_exp e1 ^ "."))
    | BVar i, BVar i' -> assert (i = i'); []
    | Clos(e1, e2), Clos(e1', e2') -> unify2 e1 e1' e2 e2'
    | EmptyS, EmptyS -> []
    | Shift n, Shift n' -> []
    | Comma(e1, e2), Comma(e1', e2') -> unify2 e1 e1' e2 e2'
    | Subst(e1, e2), Subst(e1', e2') -> unify2 e1 e1' e2 e2'
    | Nil, Nil -> []
    | Annot(e1, e2), Annot(e1', e2') -> unify2 e1 e1' e2 e2'
    | Under, _ -> []
    | _, Under -> []
    | _, _ ->
       raise (Error.Error ("Expression " ^ print_exp e1 ^ " does not unify with " ^ print_exp e2 ^ "."))
  in
  Debug.print (fun () -> "Resulted in: " ^ print_subst sigma);
  sigma

and unify2 e1 e1' e2 e2' =
  let sigma1 = unify e1 e1' in
  let sigma2 = unify (subst_list sigma1 e2) (subst_list sigma1 e2') in
  sigma1 @ sigma2

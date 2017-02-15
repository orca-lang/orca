open Syntax.Int

(* Only alpha equality for now.
   Computation happens elsewhere.
   Syntactic framework equality is coming
*)
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
       print_string (">>> " ^ print_exp e1) ; print_newline ();
       print_string ("<<< " ^ print_exp e2) ; print_newline ();
       false
  in
  Debug.print (fun () -> "Comparing: " ^ print_exp e1 ^ " and " ^ print_exp e2) ;
  let res = eq [] e1 e2 in
  Debug.print (fun () -> "Resulted in: " ^ string_of_bool res) ;
  res

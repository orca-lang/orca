open Syntax.Int
open Sign

let rec whnf (sign : signature) (e : exp) : exp =
  Debug.print (fun () -> "Computing the whnf of " ^ print_exp e ^ ".") ;
  Debug.indent();
  let res = match e with
  | Const n ->
     begin match lookup_sign_def n sign with
     | Some e -> whnf sign e
     | None -> Const n
     end
  | App(h, sp) ->
     begin match whnf sign h with
     | Fn(xs, e) ->
        let sigma = List.map2 (fun x e -> x, e) xs sp in
        whnf sign (subst_list sigma e) (* Beta reduction *)
     | e -> e
     end
  | Annot(e, _) -> e

  | e -> e (* No reduction necessary *)
  in
  Debug.deindent();
  Debug.print (fun () -> "Whnf of " ^ print_exp e ^ " is " ^ print_exp res ^ ".");
  res

open Syntax.Int
open Signature


let rec whnf (sign : signature) (e : exp) : exp =
  Debug.print (fun () -> "Computing the whnf of " ^ print_exp e ^ ".") ;
  Debug.indent();
  let res = match e with
  | Const n ->
     begin match lookup_sign_def n sign with
     | Some e -> e
     | None -> Const n
     end
  | App(Const n, e) ->
       begin match lookup_sign_def n sign with
       | Some e' -> whnf sign (App (e', e))
       | None -> App(Const n, e)
       end
  | App(Annot(Fn(x, e), t), e') ->
     begin match whnf sign t  with
     | Pi(None, s, t) -> Annot(subst (x, Annot(e', s)) e, t)
     | Pi(Some y, s, t) -> Annot(subst (x, Annot(e', s)) e, subst (y, Annot(e', s)) t)
     | _ -> raise (Error.Error "I don't really know what to make of this")
     end
  | Annot(e, _) -> e

  | e -> e (* No reduction necessary *)
  in
  Debug.deindent();
  Debug.print (fun () -> "Whnf of " ^ print_exp e ^ " is " ^ print_exp res ^ ".");
  res

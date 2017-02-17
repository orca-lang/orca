open Syntax.Int
open Signature


let rec whnf (sign : signature) (e : exp) : exp =
  Debug.print (fun () -> "Computing the whnf of " ^ print_exp e ^ ".") ;
  Debug.indent();
  let res = match e with
  | Const n ->
     begin match lookup_sign_def n sign with
     | Some e -> whnf sign e
     | None -> Const n
     end
  | App(e, e') -> assert false
  (*    begin match whnf sign e with *)
  (*    | Fn(x, e) -> whnf sign (subst (x, e') e) (\* Beta reduction *\) *)
  (*    | e -> e *)
  (*    end *)
  | Annot(e, _) -> e

  | e -> e (* No reduction necessary *)
  in
  Debug.deindent();
  Debug.print (fun () -> "Whnf of " ^ print_exp e ^ " is " ^ print_exp res ^ ".");
  res

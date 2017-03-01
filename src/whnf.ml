open Syntax.Int
open Sign

exception Matching_failure of pat * exp

let rec match_pat sign p e =
  let e = whnf sign e in
  Debug.print (fun () -> "Matching pattern " ^ print_pat p ^ " against term " ^ print_exp e);
  match p, e with
  | Innac _, _ -> []
  | PVar n, e -> [n, e]
  | PConst (n, []), Const n' when n = n' -> []
  | PConst (n, ps), App(Const n', sp) when n = n' ->
     match_pats sign ps sp
  | PConst (n, _), App(Const n', _) ->
     raise (Matching_failure (p, e))
  | _ -> raise (Matching_failure (p, e))

(* | PBVar i -> *)
(* | PLam (f, p) -> *)
(* | PAnnot (p, e) -> *)
(* | PClos (n, p) -> *)
(* | PEmptyS -> *)
(* | PShift i -> *)
(* | PSubst (p1, p2) -> *)
(* | PNil -> *)
(* | PComma (p1, p2) -> *)
(* | PUnder -> *)
(* | PWildcard -> *)

and match_pats sign ps es =
  List.concat (List.map2 (match_pat sign) ps es)


and reduce_with_clause sign sp (pats, rhs) =
  Debug.print (fun () -> "Matching spine " ^ print_exps sp ^ " against patterns " ^ print_pats pats);
  begin try
      let sigma = match_pats sign pats sp in
      match rhs with
      | Just e -> Some (subst_list sigma e) (* TODO this should call whnf *)
      | Impossible _ -> raise (Error.Violation "This case is impossible, it did not happen!")
    with
      Matching_failure (p, e) ->
      Debug.print (fun () -> "Term " ^ print_exp e ^ " failed to match against pattern " ^ print_pat p);
      None
  end

and reduce_with_clauses sign sp cls =
  let rec split n sp =
    match n, sp with
    | 0, _ -> [], sp
    | _, p :: sp' ->
       let sp1, sp2 = split (n-1) sp' in
       p :: sp1, sp2
    | _ -> raise (Error.Violation "This will not happen")
  in
  let rec reduce sp =
    function
    | [] -> None
    | cl::cls ->
       begin match reduce_with_clause sign sp cl with
       | None -> reduce sp cls
       | otw -> otw
       end
  in
  let cl_l = List.length (fst (List.hd cls)) in
  if List.length sp < cl_l then
    None
  else
    let sp1, sp2 = split cl_l sp in
    match reduce sp1 cls with
    | None -> raise (Error.Error ("Coverage error"))
    | Some e -> Some (e, sp2)


and whnf (sign : signature) (e : exp) : exp =
  Debug.print (fun () -> "Computing the whnf of " ^ print_exp e ^ ".") ;
  Debug.indent();
  let res = match e with
    (* this removes degenerate applications should they occur *)
    | App(App(h, sp), sp') ->
       whnf sign (App(h, sp @ sp'))
    | App(h, []) ->
       whnf sign h

    | Const n ->
       begin match lookup_sign_def n sign with
       | D e -> whnf sign e
       | _ -> Const n
       end
    | App(Const n, sp) ->
       begin match lookup_sign_def n sign with
       | D e -> whnf sign (App (e, sp))
       | P cls ->
          begin match reduce_with_clauses sign sp cls with
          | None -> App (Const n, sp)
          | Some (e, []) -> whnf sign e
          | Some (e, sp) -> whnf sign (App (e, sp))
          end
       | _ -> App(Const n, sp)
       end
    | App(h, sp) ->
       begin match whnf sign h with
       | Fn(xs, e) ->
          let sigma = List.map2 (fun x e -> x, e) xs sp in
          whnf sign (subst_list sigma e) (* Beta reduction *)
       | h -> App(h, sp)
       end

    | Annot(e, _) -> e
    | e -> e (* No reduction necessary *)
  in
  Debug.deindent();
  Debug.print (fun () -> "Whnf of " ^ print_exp e ^ " is " ^ print_exp res ^ ".");
  res

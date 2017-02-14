open Syntax.Int

type signature = (def_name * exp) list
let lookup_sign n sign =
  try
    List.assoc n sign
  with Not_found -> raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))

type ctx = (name * exp) list

let rec infer (sign, cG : signature * ctx) (e : exp) : exp =
  match e with
  | Annot (e, t) ->
     check (sign, cG) e t ; t
  | Const n ->
     lookup_sign n sign
  | Var n ->
     let string_ctx = ">>>" ^ (String.concat "," (List.map (fun (x, e) -> print_name n ^ ": " ^ print_exp e) cG)) ^ "<<<" in
     begin
       try List.assoc n cG
       with Not_found ->
         raise (Error.Violation
                  ("Unbound var after preprocessing, this cannot happen. (Var: " ^ print_name n ^ ")\n" ^ string_ctx))
     end
  | App (e1, e2) ->
     begin match infer (sign, cG) e1 with
     | Pi (None, s, t) ->
        check (sign, cG) e2 t ;
        t
     | Pi (Some n, s, t) ->
        check (sign, cG) e2 t ;
        subst (n, e2) t
     | _ -> raise (Error.Error "Unexpected type")
     end

  | _ -> raise (Error.Error "Cannot infer the type of this expression")

and check (sign , cG : signature * ctx) (e : exp) (t : exp) : unit =
  match e, Whnf.whnf t with
  (* types and checkable terms *)
  | Star, Set 0 -> ()
  | Set n, Set n' ->
     if n+1 = n' then ()        (* Non cummulative universes *)
     else raise (Error.Error "Wrong universe. That's a huge mistake fella!")
  | Pi (Some x, s, t), Star ->
     let _ = infer_universe (sign, cG) s in
     check (sign, (x , s) :: cG) t Star

  | Pi (Some x, s, t), Set n ->
     let n' = infer_universe (sign, cG) s in
     if n' <= n
     then check (sign, (x , s) :: cG) t (Set n)
     else raise (Error.Error "Size problem in a Π type.")

  | Pi (None, s, t), Star ->
     let _ = infer_universe (sign, cG) s in
     check (sign, cG) t Star
  | Pi (None, s, t), Set n ->
     let n' = infer_universe (sign, cG) s in
     if n' <= n
     then check (sign, cG) t (Set n)
     else raise (Error.Error "Size problem in a function type.")

  | Box (ctx, e), Set 0 ->
     (* TODO: only if ctx is a context and e is a syntactic type *)
     ()

  | Fn (f, e), Pi(None, s, t) ->
     check (sign, (f, s)::cG) e t
  | Fn (f, e), Pi(Some n, s, t) ->
     check (sign, (f, s)::cG) e (subst (n, Var f) t)

  (* terms from the syntactic framework *)
  | Lam (f, e), _ -> assert false
  | AppL (e1, e2), _ -> assert false
  | BVar i, _ -> assert false
  | Clos (e1, e2), _ -> assert false
  | EmptyS, _ -> assert false
  | Shift n, _ -> assert false
  | Comma (e1, e2), _ -> assert false
  | Subst (e1, e2), _ -> assert false
  | Nil, _ -> assert false
  | Arr (t, e), _ -> assert false

  | _ ->
     let t' =
       try infer (sign, cG) e
       with Error.Error _ -> raise (Error.Error "Cannot check expression")
     in
     if Eq.eq t t' then ()
     else
       let string_e = print_exp e in
       let string_t = print_exp t in
       let string_t' = print_exp t' in
       let message = "Expression: " ^ string_e
                     ^ "\nwas inferred type: " ^ string_t'
                     ^ "\nwhich is not equal to: " ^ string_t ^ " that was checked against."
       in
       raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))

(* infers the type of e, and it has to be something of kind set_n *)
(* no normalization happens here *)
and infer_universe (sign, cG : signature * ctx) : exp -> int =
  let f e = infer_universe (sign, cG) e in
  function
  | Star -> 0
  | Set n -> n + 1
  | Box (ctx, e) ->
     (* TODO we need to check that e is of a syntactic type
        with another judgement (aka function)
      *)
     0
  | Pi (_, s, Star) -> 0
  | Pi (_, s, t) -> max (f s) (f t)

  | Const n -> f (lookup_sign n sign)
  | App(e1, e2) ->
     begin match infer (sign, cG) e1 with
     | Pi (Some x, s, t) ->
        let _  = check (sign, cG) e2 s in
        (* we infer the type after substituting for e in the pitype *)
        infer_universe (sign, cG) (subst (x, e2) t)
     | Pi (None, s, t) ->
        let _  = check (sign, cG) e2 s in
        infer_universe (sign, cG) t

     | _ -> raise (Error.Error "Element in function position not of function type")
     end

  | _ -> raise (Error.Error "Not a canonical type")

  (* | Arr (t, e) -> "(->> " ^ print_exp t ^ " " ^ print_exp e ^ ")" *)
  (* | Fn (f, e) -> "(fn " ^ print_name f ^ " " ^ print_exp e ^ ")" *)
  (* | Lam (f, e) -> "(\ " ^ print_name f ^ " " ^ print_exp e ^ ")" *)
  (* | App (e1, e2) -> "(app " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")" *)
  (* | AppL (e1, e2) -> "(' " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")" *)
  (* | Const n -> print_name n *)
  (* | Var n -> print_name n *)
  (* | BVar i -> "(i " ^ string_of_int i ^ ")" *)
  (* | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")" *)
  (* | EmptyS -> "^" *)
  (* | Shift n -> "^" ^ string_of_int n *)
  (* | Comma (e1, e2) -> "(, " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")" *)
  (* | Nil -> "0" *)
  (* | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")" *)


let tc_constructor (sign : signature) (universe : exp) (n , ct : def_name * exp) : signature =
  check (sign, []) ct universe ;
  (n, ct) :: sign


let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, e, ds) ->
     let t = List.fold_left (fun t2 (_, n, t1) -> Pi(Some n, t1, t2)) e ps in
     let univ = infer_universe (sign, []) t in
     let u = if univ == 0 then Star else Set (univ - 1) in (* MMMMM Hack alert this may be wrong! *)
     List.fold_left (fun sign decl -> tc_constructor sign u decl) ((n, t)::sign) ds

  | Syn (n, ps, e, ds) ->
     assert false
  | DefPM (n, e, ds) -> assert false
  | Def (n, t, e) -> assert false

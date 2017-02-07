open Syntax.Int

type signature = (def_name * exp) list
let lookup_sign n sign = List.assoc n sign

type ctx = (name * exp) list

let rec infer (sign , cG : signature * ctx) (e : exp) : exp =
  match e with
  | Annot (e1, e2) -> assert false
  | Const n -> assert false
  | Var n -> assert false
  | App (e1, e2) -> assert false

  | _ -> raise (Error.Error "Cannot infer the type of this expression")

and check (sign , cG : signature * ctx) (e : exp) (t : exp) : unit =
  match e with
  (* types and checkable terms *)
  | Star -> assert false
  | Set n -> assert false
  | Pi (Some n, s, t) -> assert false
  | Pi (None, s, t) -> assert false
  | Arr (t, e) -> assert false
  | Box (ctx, e) -> assert false

  | Fn (f, e) -> assert false

  (* terms from the syntactic framework *)
  | Lam (f, e) -> assert false
  | AppL (e1, e2) -> assert false
  | BVar i -> assert false
  | Clos (e1, e2) -> assert false
  | EmptyS -> assert false
  | Shift n -> assert false
  | Comma (e1, e2) -> assert false
  | Subst (e1, e2) -> assert false
  | Nil -> assert false

  | _ ->
     let t' = infer (sign, cG) e in
     if Eq.eq t t'
     then ()
     else raise (Error.Error "Term's inferred type is not equal to checked type.")

(* infers the type of e, and it has to be something of kind set_n *)
(* no normalization happens here *)
let rec infer_universe (sign : signature) : exp -> int =
  function
  | Star -> 0
  | Set n -> n + 1
  | Box (ctx, e) ->
     (* TODO we need to check that e is of a syntactic type
        with another judgement (aka function)
      *)
     0
  | Pi (_, s, Star) -> 0
  | Pi (_, s, t) -> max (infer_universe sign s) (infer_universe sign t)

  | Const n -> infer_universe sign (lookup_sign n sign)
  | App(e1, e2) ->
     begin match infer (sign, []) e1 with (* TODO empty cG context? *)
     | Pi (Some x, s, t) ->
        let _  = check (sign, []) e2 s in
        (* we infer the type after substituting for e in the pitype *)
        infer_universe sign (subst (x, e2) t)
     | Pi (None, s, t) ->
        let _  = check (sign, []) e2 s in
        infer_universe sign t

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


let tc_constructor ((n , t) : name * exp) : unit =
  assert false

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, e, ds) ->
     let t = List.fold_left (fun t2 (_, n, t1) -> Pi(Some n, t1, t2)) e ps in
     let _ = infer_universe sign t in
     (* typecheck ds *)
     assert false

  | Syn (n, ps, e, ds) ->
     assert false
  | DefPM (n, e, ds) -> assert false
  | Def (n, t, e) -> assert false

open Syntax.Int

type signature = (def_name * exp) list
let lookup n sign = List.assoc n sign

let rec infer (e : exp) : exp = assert false
and check (e : exp) (t : exp) : unit = assert false

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

  | Const n -> infer_universe sign (lookup n sign)
  | App(Const n, e) ->
     let Pi (_, s, t) = lookup n sign in
     let _ = check e s in
     (* we infer the type after substituting for e in the pitype *)
     (* infer_universe sign (subst (x, e) t) *)
     assert false
  | App(e1, e2) ->
     (* e1 has to be of pitype *)
     (* e2 has to be of the right type for e1 *)
     (* substitute and continue infering the universe *)
  (* infer_universe sign e1 *) (* Wrong!! *)
     assert false


  | _ -> assert false (* not a type? *)

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

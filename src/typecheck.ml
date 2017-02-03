open Syntax.Int

type signature = (name * exp) list

let rec infer (e : exp) : exp = assert false
and check (e : exp) : unit = assert false

(* infers the type of e, and it has to be something of kind set_n *)
(* no normalization happens here *)
let rec infer_universe (sign : signature) : exp -> int =
  function
  | Star -> 0
  | Set n -> n + 1
  | Box (ctx, e) -> 0
  | Pi (_, s, Star) -> 0
  | Pi (_, s, t) -> max (infer_universe sign s) (infer_universe sign t)

  | Const n
  | App(Const n, _) -> infer_universe sign (List.assoc n sign)
  | App(e1, e2) -> infer_universe sign e1
  (* | Const n -> assert false (\* a constant from the signature,needs its type looked up *\) *)

  | _ -> assert false (* not a canonical type? *)

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

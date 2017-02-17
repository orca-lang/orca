open Syntax.Int
open Signature

type ctx_map = pat list

let rec to_head_spine (sign : signature) : exp -> exp * exp list = function
  | App (e1, e2) ->
     (* let h, sp = to_head_spine sign (Whnf.whnf sign e1) in *)
  (* h, (sp @ [e2]) *)
     assert false
  | Const n -> Const n, []
  | _ -> raise (Error.Violation "Term is not convertible to head/spine form.")

let rec create_ctx (p : pats) (t : exp) : ctx * exp = assert false
  (* match p, t with *)
  (* | [], _ -> [], t *)
  (* | p :: ps, Pi (Some n, s, t) -> *)
  (*    let g, t' = create_ctx ps t in *)
  (*    (n, s) :: g, t' *)
  (* | p :: ps, Pi (None, s, t) -> *)
  (*    let g, t' = create_ctx ps t in *)
  (*    (gen_name "_", s) :: g, t' *)
  (* | p :: ps, _ -> *)
  (*    raise (Error.Error "Pattern spine is too long when comparing with type") *)

let rec matching (sigma : ctx_map) (p : pats) : pats =
  match sigma, p with
  | [], [] -> []
  | PVar n :: sigma', p :: ps -> p :: matching sigma' ps
  | Innac _ :: sigma', p :: ps -> matching sigma' ps
  | _ -> assert false

let split (p : pats) (cD : ctx) : ctx * ctx_map =
  match p, cD with
  (* | [], [] -> [], [] *)
  (* | PConst (c, ps) :: ps', (x, t) :: cD' -> *)
  (*    let Const n, spine = to_head_spine t in *)
  (*    let  *)
  | _, _ -> assert false

let compose_maps (sigma : ctx_map) (delta : ctx_map) : ctx_map =
  assert false

let refine (p : pats) (cD : ctx) (sigma : ctx_map) (cG : ctx) : pats * ctx * ctx_map =
  let cD', delta = split p cD in
  let p' = matching delta p in
  let sd = compose_maps sigma delta in
  p' , cD', sd

let check_pats (p : pats) (cG : ctx) : ctx * ctx_map =
  assert false

let rec check_innac (cD : ctx) (p : pats) (sigma : ctx_map) (cG : ctx) : unit =
  assert false

let check_lhs (p : pats) (cG : ctx) : ctx * ctx_map =
  let cD, sigma = check_pats p cG in
  check_innac cD p sigma cG;
  cD, sigma

let check_clause (f : def_name) (p : pats) (rhs : exp) (t : exp) : unit =
  let g, t' = create_ctx p t in

  assert false

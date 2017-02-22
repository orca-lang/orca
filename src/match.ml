open Syntax.Int
open Sign
open Check


type ctx_map = pat list

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

let check_clause (sign : signature) (f : def_name) (p : pats) (telG : tel) (t : exp) (rhs : rhs) : unit =
  let cD, sigma = check_lhs p (ctx_of_tel telG) in
  match rhs with
  | Just e -> check (sign, cD) e t
  | Impossible x ->
  assert false

open Syntax.Int
open Sign
open Check
open Name


type ctx_map = pat list

let compose_maps (sigma : ctx_map) (delta : ctx_map) : ctx_map =
  assert false

let rec matching (sigma : ctx_map) (p : pats) : pats =
  match sigma, p with
  | [], [] -> []
  | PVar n :: sigma', p :: ps -> p :: matching sigma' ps
  | Innac _ :: sigma', p :: ps -> matching sigma' ps
  | _ -> assert false

let rec flexible (p : pats)(cG : ctx) : name list =
  match p, cG with
  | [], [] -> []
  | Innac e::ps, (x, t)::cG' -> x::(flexible ps cG')
  | p::ps, (x, t)::cG' -> flexible ps cG'
  | _ -> raise (Error.Violation ("Flexible: length violation."))

let split (sign : signature) (p : pats) (cD : ctx) : ctx * ctx_map =
  match p, cD with
  | [], [] -> [], []
  | PConst (c, ps) :: ps', (x, t) :: cD' ->
     begin match Whnf.whnf sign t with
     | App(Const n, sp) ->
        let us, vs = split_idx_param n sp in
        begin match lookup_sign_entry c sign with
        | Constructor (c, thetatel, (n', sp)) ->
           if n != n' then raise (Error.Error "Get a grip!, wrong constructor.")
           else
             let us', ws = split_idx_param n sp in
             (* let flex = flexible ps (ctx_of_tel thetatel) in *)
             (* let delta = Unify.unify_flex sign flex vs ws in *)
             (* let delta' = PConst (c, elist_of_tel subst_list_on_tel delta thetatel) :: (pat_of_exp delta) in *)
             assert false

        | _ -> assert false

        end

     | _ -> raise (Error.Error "This should allow for better error messages if I were not that lazy.")
     end
  | _, _ -> assert false


let refine (sign : signature) (p : pats) (cD : ctx) (sigma : ctx_map) : pats * ctx * ctx_map =
  let cD', delta = split sign p cD in
  let p' = matching delta p in
  let sd = compose_maps sigma delta in
  p' , cD', sd

let check_pats (sign : signature) (p : pats) (cG : ctx) : ctx * ctx_map =
  let is_Pvar = function
    | PVar _ -> true
    | _ -> false
  in
  let rec check_pats (p : pats) (sigma : ctx_map) (cD : ctx) : ctx * ctx_map =
    if List.for_all is_Pvar p then
      cD, sigma
    else
      let p', cD', sigma' = refine sign p cD sigma in
      check_pats p' sigma' cD'
  in
  check_pats p (List.map (fun (x, _) -> PVar x) cG) cG


let rec check_innacs (sign, cD : signature * ctx) (p : pats) (sigma : ctx_map) (cG : ctx) : unit =
  match p, sigma with
  | p::ps, q::qs ->
     begin match cG with
     | (x, t) :: cG' -> check_innac (sign, cD) p q t ; check_innacs (sign, cD) ps qs (ctx_subst (x, exp_of_pat q) cG)
     | _ -> raise (Error.Error "The context ended unexpectedly.")
     end
  | [], [] -> ()
  | _ -> raise (Error.Error "Size mismatch.")

and check_innac (sign, cD : signature * ctx) (p : pat) (q : pat) (t : exp) : unit =
  match p, q with
  | Innac ep, Innac eq ->
     check (sign, cD) ep t ;
     check (sign, cD) eq t ;
     let _ = Unify.unify sign ep eq in
     ()
  | PVar x, PVar y when x = y -> ()
  | PConst (n, sp), PConst (n', sq) when n = n' ->
     begin match lookup_sign_entry n sign with
     | Constructor (_, tel, _) -> check_innacs (sign, cD) sp sq (ctx_of_tel tel)
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | _ -> assert false

let check_lhs (sign : signature) (p : pats) (cG : ctx) : ctx * ctx_map =
  let cD, sigma = check_pats sign p cG in
  check_innacs (sign, cD) p sigma cG ;
  cD, sigma

let caseless (sign : signature) (cD : ctx) (x : name) (t : exp) : unit =
  if [] = (* snd(split sign [PVar x] ((x, t) :: cD)) *) assert false
  then ()
  else raise (Error.Error ("Pattern variable " ^ print_name x ^ " is not really impossible."))


let check_clause (sign : signature) (f : def_name) (p : pats) (telG : tel) (t : exp) (rhs : rhs) : unit =
  let cD, sigma = check_lhs sign p (ctx_of_tel telG) in
  match rhs with
  | Just e -> check (sign, cD) e t
  | Impossible x -> caseless sign cD x t

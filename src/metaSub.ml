open Name
open Syntax.Int
open Print.Int

let rec append_bctx cP cP' =
  match cP with
  | Nil -> cP'
  | CtxVar _ -> raise (Error.Violation "Appended a bctx terminating with a CtxVar to another bctx")
  | Snoc (cP, x, e) -> Snoc (append_bctx cP cP', x, e)

let lookup_bound_name cP x =
  let rec lookup cP0 i =
    match cP0 with
    | Snoc (_, x', t) when x = x' -> i, Clos(t, Shift (i+1), cP)
    | Snoc (cP', _, _) -> lookup cP' (i+1)
    | _ -> raise (Error.Error ("Bound variable " ^ x ^ " not found in bound context"))
  in
  lookup cP 0

let lookup_bound cP x =
  let rec lookup cP0 i =
    match cP0 with
    | Snoc (_, _, t) when i = 0 -> Clos(t, Shift (x+1), cP)
    | Snoc (cP', _, _) -> lookup cP' (i-1)
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup cP x

let rec bctx_of_lam_stel (fs : string list) (tel : stel) (cP : bctx) : bctx * stel=
    match fs, tel with
    | [], tel' -> cP, tel'
    | f::fs', (_, _, t)::tel' ->
       let cP, tel'' = bctx_of_lam_stel fs' tel' cP in
       Snoc (cP , f, t), tel''
    | _, [] -> raise (Error.Error ("Too many variables declared in lambda"))

let bctx_of_stel cP tel =
  let rec make = function
    | [] -> cP
    | (_, x, s)::tel' -> Snoc (make tel', x, s)
  in
  make (List.rev tel)

let rec bctx_of_ctx_exp = function
  | Snoc(g, x, e) -> Snoc(bctx_of_ctx_exp g, x, e)
  | _ -> Nil

let drop_suffix cP n =
    let rec drop cP' n' =
      match cP', n' with
      | _, 0 -> cP'
      | Snoc(cP', _, _), n' -> drop cP' (n'-1)
      | _ -> raise (Error.Error ("Tried to drop " ^ string_of_int n ^ " terms out of " ^ print_bctx cP ^ " which is too short."))
    in
    drop cP n

 let keep_suffix cP n =
    let rec keep cP' n' =
      match cP', n' with
      | _, 0 -> Nil
      | Snoc(cP', x, t), n' -> Snoc(keep cP' (n'-1), x, t)
      | _ -> raise (Error.Error ("Tried to keep " ^ string_of_int n ^ " terms out from " ^ print_bctx cP ^ " which is too short."))
    in
    keep cP n



let rec beautify_bound_name x cP =
  let rec count = function
    | CtxVar _
      | Nil -> 0
    | Snoc (cP', x', _) when x = x' -> 1 + count cP'
    | Snoc (cP', x', _) -> count cP'
  in
  let c = count cP in
  if c = 0 then x
  else x ^ string_of_int c

let rec beautify_bound_names xs cP =
  match xs with
  |[] -> []
  | x::xs ->
    let x' = beautify_bound_name x cP in
    x'::beautify_bound_names xs (Snoc (cP, x, Star)) (* star is a dummy type *)

let rec beautify_idx i cP =
  if not (do_beautify ()) then None
  else match i, cP with
  | _, CtxVar _
  | _, Nil -> None
  | 0, Snoc(cP', x, _) -> Some (beautify_bound_name x cP')
  | i, Snoc(cP', _, _) -> beautify_idx (i-1) cP'


(* Applying syntactic substitutions *)

(* let syn_subst_stel (sigma : exp) (cP : bctx) (tel : stel) : stel * exp = *)
(*   let rec do_something i cP tel = *)
(*     match tel with *)
(*     | [] -> [], i *)
(*     | (icit, n, tt)::tel' -> *)
(*        let tel'', i' = do_something (i+1) (Snoc (cP, n, tt)) tel' in *)
(*        (icit, n, Clos(tt, ShiftS (i, sigma), cP))::tel'', i' *)
(*   in *)
(*   let tel', i = do_something 0 cP tel in *)
(*   tel', ShiftS (i, sigma) *)

(* let rec ss_syn_subst_spi (e : exp) cP (tel : stel) : stel * exp = *)
(*   syn_subst_stel (Dot (Shift 0, e)) cP tel *)

(* let rec ss_syn_subst_stel (e : exp) (tel : stel) : stel = *)
(*   fst (ss_syn_subst_spi e tel) *)

(* let rec syn_subst_spi (sigma : exp) (tel : stel) (t : exp) : stel * exp = *)
(*   let tel', sigma' = syn_subst_stel sigma tel in *)
(*   tel', Clos(t, sigma') *)


module E = Syntax.Ext
module I = Syntax.Int

type sign = (E.name * I.name) list (* The signature for types *)
type ctx = (E.name * I.name) list  (* The context for regular variables *)
type bctx = E.name list            (* The context for bound variables *)

let rec lookup n = function
  | (n', nn) :: _ when n = n' -> Some nn
  | _ :: xs -> lookup n xs
  | [] -> None

let index n cP =
  let rec index n i = function
    | n' :: _ when n = n' -> Some i
    | _ :: xs -> index n (i + 1) xs
    | [] -> None
  in
  index n 0 cP

(* Finds a name in the signature or the context and returns the
   appropriate internal expression *)
let find_name (sign : sign) (cG : ctx) (cP : bctx) (n : E.name) : I.exp =
  match index n cP with
  | Some i -> I.BVar i
  | None -> match lookup n cG with
            | Some n -> I.Var n
            | None -> match lookup n sign with
                       | Some n -> I.Const n
                       | _ -> raise (Error.Error ("Unbound variable: " ^ n))

let add_name c n = let nn = I.gen_name n in ((n, nn) :: c), nn
let add_name_bvar c n : bctx * I.name = let nn = I.gen_name n in (n :: c), nn

let rec get_bound_var_ctx (e: E.exp) : bctx =
  match e with
  | E.Comma (g, E.Annot(E.Ident n, _)) -> n :: (get_bound_var_ctx g)
  | E.EmptyS -> []
  | _ -> []

let rec pproc_exp (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : I.exp =
  let f = pproc_exp s cG cP in
  match e with
  | E.Star -> I.Star
  | E.Set n -> I.Set n
  | E.Arr (E.Annot (E.Ident n, t0), t1) ->
     let cG', n' = add_name cG n in
     I.Pi (n', f t0, pproc_exp s cG cP t1)
  | E.Arr (s, t) -> I.Arr(f s, f t)
  | E.Box (g, e) ->
     let cP' = get_bound_var_ctx g in
     I.Box(pproc_exp s cG cP' g, pproc_exp s cG cP' e)
  | E.Fn (n, e) ->
     let cG', n' = add_name cG n in
     I.Fn(n', pproc_exp s cG' cP e)
  | E.Lam (n, e) ->
     let cP', n' = add_name_bvar cP n in
     I.Lam(n', pproc_exp s cG cP' e)
  | E.App (e1, e2) -> I.App(f e1, f e2)
  | E.AppL (e1, e2) -> I.AppL(f e1, f e2)
  | E.Ident n -> find_name s cG cP n
  | E.Clos (e, s) -> I.Clos(f e, f s)
  | E.EmptyS -> I.EmptyS
  | E.Shift n -> I.Shift n
  | E.Comma (e1, e2) -> I.Comma(f e1, f e2)
  | E.Nil -> I.Nil
  | E.Annot (e1, e2) -> I.Annot(f e1, f e2)

let pproc_decl s (n, e) =
  let s', n' = add_name s n in
  s', (n', pproc_exp s [] [] e)
let pproc_param s cG (icit, n, e) =
  let cG', n' = add_name cG n in
  cG', (icit, n', pproc_exp s cG [] e)

let pproc_pat s cG n =
  let cG', n' = add_name cG n in
  cG', n' (* this is convoluted, but it will be like this once patterns are really defined *)

let pproc_def_decl s (pats, e) =
  let cG', pats' = List.fold_left (fun (cG, pats) pat -> let cG', pat' = pproc_pat s cG pat in cG', (pat'::pats)) (s, []) pats in
  (pats', pproc_exp s cG' [] e)

let pre_process s = function
  | E.Data (n, ps, e, ds) ->
     let _, ps' = List.fold_left (fun (cG, ps) p -> let cG', p' = pproc_param s cG p in cG', (p'::ps)) (s, []) ps in
     let e' = pproc_exp s [] [] e in
     let s', n' = add_name s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s d in ss, (dd :: dos)) (s', []) ds in
     s'', I.Data (n', ps', e', ds')
  | E.Syn (n, ps, e, ds) ->
     let _, ps' = List.fold_left (fun (cG, ps) p -> let cG', p' = pproc_param s cG p in cG', (p'::ps)) (s, []) ps in
     let e' = pproc_exp s [] [] e in
     let s', n' = add_name s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s d in ss, (dd :: dos)) (s', []) ds in
     s'', I.Syn (n', ps', e', ds')
  | E.DefPM (n, e, ds) ->
     let s', n' = add_name s n in
     s', I.DefPM (n', pproc_exp s [] [] e, List.map (pproc_def_decl s') ds)
  | E.Def (n, t, e) ->
     let s', n' = add_name s n in
     s', I.Def (n', pproc_exp s [] [] t, pproc_exp s [] [] e)

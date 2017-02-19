(**
   This module processes the external syntax into internal syntax.

   Its duties are:

   * Refine the tree for ambiguous constructs, like:
     - add pi types
     - remove "term boxes" as they only are needed for indexing
     - remove all arrows into nameless pis
   * Ensure that are variables and constructors are well-scoped
   * Index bound variables to de Bruijn indices
   * Manage repeated names (TO BE DONE)

 *)

module E = Syntax.Ext
module I = Syntax.Int


type sign = E.name list (* The signature for types *)
type ctx = (E.name * Name.name) list  (* The context for regular variables *)
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
            | None ->
               if List.mem n sign
               then I.Const n
               else raise (Error.Error ("Unbound variable: " ^ n))

let add_name_sign sign n = n :: sign
let add_name_ctx c n = let nn = Name.gen_name n in ((n, nn) :: c), nn
let add_name_bvar c n : bctx = n :: c

let isEmpty = (=) []

let find_pat_name (s : sign) (cG : ctx) (cP : bctx) (n : E.name) : ctx * I.pat =
    begin
      match index n cP with
      | Some i -> cG, I.PBVar i
      | None ->
        if List.mem n s then
          cG, I.PConst (n, [])
        else
          begin
            match lookup n cG with
            | Some _ -> raise (Error.Error ("Repeated variable " ^ n ^ " in pattern spine"))
            | None ->
              let cG', n' = add_name_ctx cG n in
              cG', I.PVar n'
          end
    end

let rec get_bound_var_ctx (e: E.exp) : bctx =
  match e with
  | E.Comma (g, E.Annot(E.Ident n, _)) -> n :: (get_bound_var_ctx g)
  | E.Nil -> []
  | _ -> []

let rec get_bound_var_ctx_no_annot (e : E.exp) : bctx =
  match e with
  | E.Comma (g, E.Annot(E.Ident n, _)) -> n :: (get_bound_var_ctx_no_annot g)
  | E.Comma (g, E.Ident n) -> n :: (get_bound_var_ctx_no_annot g)
  | E.Nil -> []
  | E.Ident _ -> []
  | e -> raise (Error.Error (E.print_exp e ^ " is a forbidden expression on the left hand side of :>"))

let rec get_bound_var_ctx_in_pat (p : E.pat) : bctx =
  match p with
  | E.PComma (g, E.PAnnot(E.PIdent n, _)) -> n :: (get_bound_var_ctx_in_pat g)
  | E.PComma (g, E.PIdent n) -> n :: (get_bound_var_ctx_in_pat g)
  | E.PNil -> []
  | E.PIdent _ -> []
  | p -> raise (Error.Error (E.print_pat p ^ " is a forbidden pattern on the left hand side of :>"))

let rec pproc_exp (s : sign) (cG : ctx) (cP : bctx) : E.exp -> I.exp =
  let f e = pproc_exp s cG cP e in
  function
  | E.Star -> I.Star
  | E.Set n -> I.Set n
  | E.Arr (t0, t1) ->
     let tel, t' = pproc_tel s cG cP (E.Arr (t0, t1)) in
     I.Pi (tel, t')
  | E.SArr (s, t) -> I.Arr(f s, f t)
  | E.Box (g, e) ->
    if isEmpty cP then
     let cP' = get_bound_var_ctx g in
     I.Box(pproc_exp s cG cP' g, pproc_exp s cG cP' e)
    else
      raise (Error.Error "Bound variables bindings (|-) cannot be nested")
  | E.TBox (g, e) ->
    if isEmpty cP then
      let cP' = get_bound_var_ctx_no_annot g in
      pproc_exp s cG cP' e
    else
      raise (Error.Error "Bound variables bindings (:>) cannot be nested")
  | E.Fn (n, e) ->
     let cG', n' = add_name_ctx cG n in
     I.Fn(n', pproc_exp s cG' cP e)
  | E.Lam (n, e) ->
     I.Lam(n, pproc_exp s cG (add_name_bvar cP n) e)
  | E.App (e1, e2) ->
     let h, sp = pproc_app s cG cP (E.App(e1, e2)) in
     I.App(h, sp)
  | E.AppL (e1, e2) -> I.AppL(f e1, f e2)
  | E.Ident n -> find_name s cG cP n
  | E.Clos (e, s) -> I.Clos(f e, f s)
  | E.EmptyS -> I.EmptyS
  | E.Shift n -> I.Shift n
  | E.Comma (e1, e2) -> I.Comma(f e1, f e2)
  | E.Semicolon (e1, e2) -> I.Subst(f e1, f e2)
  | E.Nil -> I.Nil
  | E.Annot (e1, e2) -> I.Annot(f e1, f e2)
  | E.Under -> I.Under

and pproc_tel (s : sign) (cG : ctx) (cP : bctx) : E.exp -> I.tel * I.exp =
  function
  | E.Arr (E.Annot (E.Ident n, t0), t1) ->
     let cG', n' = add_name_ctx cG n in
     let tel, t = pproc_tel s cG' cP t1 in
     I.Named (n', pproc_exp s cG cP t0) :: tel, t
  | E.Arr (t0, t1) ->
     let tel, t = pproc_tel s cG cP t1 in
     I.Unnamed (pproc_exp s cG cP t0) :: tel , t
  | t -> [], pproc_exp s cG cP t

and pproc_app (s : sign) (cG : ctx) (cP : bctx) : E.exp -> I.exp * I.exp list =
  function
  | E.App(e1, e2) ->
     let h, sp = pproc_app s cG cP e1 in
     h, sp @[pproc_exp s cG cP e2]
  | e -> pproc_exp s cG cP e, []

let pproc_decl s cG (n, e) =
  add_name_sign s n, (n, pproc_exp s cG [] e)

let pproc_param s cG (icit, n, e) =
  let cG', n' = add_name_ctx cG n in
  cG', (icit, n', pproc_exp s cG [] e)

let rec pproc_pat (s : sign) cG cP =
  let f pat = pproc_pat s cG cP pat in
  function
  | E.PIdent n -> find_pat_name s cG cP n
  | E.Innac e -> cG, I.Innac (pproc_exp s cG [] e)
  | E.PLam (x, p) ->
    let cG', p' = pproc_pat s cG (add_name_bvar cP x) p in
    cG', I.PLam (x,  p')
  | E.PConst (c, ps) ->
    let g (cG, ps) p =
      let cG', p' = pproc_pat s cG cP p in
      cG', p' :: ps
    in
    let cG', ps' = List.fold_left g (cG, []) ps in
    cG', I.PConst (c, List.rev ps')
  | E.PAnnot (p, t) ->
    let cG', p' = f p in
    cG', I.PAnnot (p', pproc_exp s [] [] t)
  | E.PClos (x, p) ->
    begin match find_pat_name s cG cP x with
    | cG', I.PVar n ->
      let cG'', p2' = pproc_pat s cG' cP p in
      cG'', I.PClos (n, p2')
    | cG', _ -> raise (Error.Error "Substitution can only be applied to pattern variables")
    end
  | E.PEmptyS -> cG, I.PEmptyS
  | E.PShift i -> cG, I.PShift i
  | E.PSubst (p1, p2) ->
    let cG', p1' = f p1 in
    let cG'', p2' = pproc_pat s cG' cP p2 in
    cG'', I.PSubst (p1', p2')
  | E.PNil -> cG, I.PNil
  | E.PComma (p1, p2) -> assert false
  | E.PBox (g, p) ->
    if isEmpty cP then
      let cP' = get_bound_var_ctx_in_pat g in
      pproc_pat s cG cP' p
    else
      raise (Error.Error "Bound variables bindings (:>) cannot be nested")
  | E.PUnder -> cG, I.PUnder
  | E.PWildcard -> cG, I.PWildcard

let pproc_def_decl s (pats, e) =
  let
    cG', pats' = List.fold_left (fun (cG, pats) pat -> let cG', pat' = pproc_pat s cG [] pat in cG', (pat'::pats)) ([], []) pats
  in
  (pats', pproc_exp s cG' [] e)

let params_to_ctx = List.map2 (fun (_, n, _) (_, n', _) -> n, n')

let pre_process s = function
  | E.Data (n, ps, e, ds) ->
     let _, ps' = List.fold_left (fun (cG, ps) p -> let cG', p' = pproc_param s cG p in cG', (p'::ps)) ([], []) ps in
     let cG = params_to_ctx ps ps' in
     let e' = pproc_exp s cG [] e in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s cG d in ss, (dd :: dos)) (s', []) ds in
     s'', I.Data (n, ps', e', ds')
  | E.Syn (n, ps, e, ds) ->
     let _, ps' = List.fold_left (fun (cG, ps) p -> let cG', p' = pproc_param s cG p in cG', (p'::ps)) ([], []) ps in
     let cG = params_to_ctx ps ps' in
     let e' = pproc_exp s cG [] e in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s cG d in ss, (dd :: dos)) (s', []) ds in
     s'', I.Syn (n, ps', e', ds')
  | E.DefPM (n, e, ds) ->
     let s' = add_name_sign s n in
     s', I.DefPM (n, pproc_exp s [] [] e, List.map (pproc_def_decl s') ds)
  | E.Def (n, t, e) ->
     let s' = add_name_sign s n in
     s', I.Def (n, pproc_exp s [] [] t, pproc_exp s [] [] e)

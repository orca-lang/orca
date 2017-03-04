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
   * Checks that constructors build the appropriate type
   * Checks that the equation list is not empty
   * Checks that all equations are of the same length

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
let rec add_names_ctx c = function
  | [] -> c, []
  | n::ns ->
     let c', n' = add_name_ctx c n in
     let c'', ns' = add_names_ctx c' ns in
     c'', n'::ns'


let add_name_bvars c n : bctx = n @ c

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
  | E.Annot(E.Ident n, _) -> [n]
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

let rec pproc_exp (s : sign) (cG : ctx) (cP : bctx) (is_syntax : bool) (e :E.exp) : I.exp =
  Debug.print (fun () -> "Preprocessing expression " ^ E.print_exp e ^ " with flag " ^ string_of_bool is_syntax);
  let f e = pproc_exp s cG cP is_syntax e in
  match e with
  | E.Star -> I.Star
  | E.Set n -> I.Set n
  | E.Ctx -> I.Ctx
  | E.Arr (t0, t1) when is_syntax ->
    let tel, t' = pproc_stel s cG cP is_syntax (E.Arr (t0, t1)) in
    I.SPi (tel, t')
  | E.SArr (t0, t1) ->
    let tel, t' = pproc_stel s cG cP is_syntax (E.Arr (t0, t1)) in
    I.SPi (tel, t')
  | E.Arr (t0, t1) ->
     let tel, t' = pproc_tel s cG cP is_syntax (E.Arr (t0, t1)) in
     I.Pi (tel, t')
  | E.Box (g, e) ->
    if isEmpty cP then
     let cP' = get_bound_var_ctx g in
     I.Box(pproc_exp s cG cP' is_syntax g, pproc_exp s cG cP' is_syntax e)
    else
      raise (Error.Error "Bound variables bindings (|-) cannot be nested")
  | E.TBox (g, e) ->
    if isEmpty cP then
      let cP' = get_bound_var_ctx_no_annot g in
      pproc_exp s cG cP' is_syntax e
    else
      raise (Error.Error "Bound variables bindings (:>) cannot be nested")
  | E.Fn (ns, e) ->
     let cG', n' = add_names_ctx cG ns in
     I.Fn(n', pproc_exp s cG' cP is_syntax e)
  | E.Lam (n, e) ->
     I.Lam(n, pproc_exp s cG (add_name_bvars cP n) is_syntax e)
  | E.App (e1, e2) ->
     let h, sp = pproc_app s cG cP is_syntax (E.App(e1, e2)) in
     I.App(h, sp)
  | E.AppL (e1, e2) ->
    let h, sp = pproc_app s cG cP is_syntax (E.AppL(e1, e2)) in
     I.AppL(h, sp)
  | E.Ident n -> find_name s cG cP n
  | E.Clos (e, s) -> I.Clos(f e, f s)
  | E.EmptyS -> I.EmptyS
  | E.Shift n -> I.Shift n
  | E.Semicolon (e1, e2) -> I.Dot(f e1, f e2)
  | E.Comma (e1, E.Annot (E.Ident x, e2)) -> I.Snoc (f e1, x, f e2)
  | E.Comma (e1, e2) -> I.Snoc (f e1, "_", f e2)
  | E.Nil -> I.Nil
  | E.Annot (e1, e2) -> I.Annot(f e1, f e2)
  | E.Under -> I.Under
  | E.Hole (Some n) -> I.Hole (Name.gen_name n)
  | E.Hole None -> I.Hole (Name.gen_name "H")

and pproc_tel (s : sign) (cG : ctx) (cP : bctx) (is_syntax : bool) : E.exp -> I.tel * I.exp =
  function
  | E.Arr (E.Annot (E.Ident n, t0), t1) ->
     let cG', n' = add_name_ctx cG n in
     let tel, t = pproc_tel s cG' cP is_syntax t1 in
     (Syntax.Explicit, n', pproc_exp s cG cP is_syntax t0) :: tel, t
  | E.Arr (t0, t1) ->
     let tel, t = pproc_tel s cG cP is_syntax t1 in
     (Syntax.Explicit, Name.gen_floating_name (), pproc_exp s cG cP is_syntax t0) :: tel , t
  | t -> [], pproc_exp s cG cP is_syntax t

and pproc_stel (s : sign) (cG : ctx) (cP : bctx) (is_syntax : bool) : E.exp -> I.stel * I.exp =
  function
  | E.Arr (E.Annot (E.Ident n, t0), t1)
  | E.SArr (E.Annot (E.Ident n, t0), t1) ->
     let cP' = add_name_bvars cP [n] in
     let tel, t = pproc_stel s cG cP' is_syntax t1 in
     (Syntax.Explicit, n, pproc_exp s cG cP is_syntax t0) :: tel, t
  | E.Arr (t0, t1)
  | E.SArr (t0, t1) ->
    let cP' = add_name_bvars cP ["_"] in
     let tel, t = pproc_stel s cG cP' is_syntax t1 in
     (Syntax.Explicit, "_", pproc_exp s cG cP is_syntax t0) :: tel , t
  | t -> [], pproc_exp s cG cP is_syntax t

and pproc_app (s : sign) (cG : ctx) (cP : bctx) (is_syntax : bool) : E.exp -> I.exp * I.exp list =
  function
  | E.App(e1, e2) ->
     let h, sp = pproc_app s cG cP is_syntax e1 in
     h, sp @[pproc_exp s cG cP is_syntax e2]
  | E.AppL(e1, e2) ->
     let h, sp = pproc_app s cG cP is_syntax e1 in
     h, sp @[pproc_exp s cG cP is_syntax e2]
  | e -> pproc_exp s cG cP is_syntax e, []

let pproc_decl s cG (n, e) (is_syntax : bool) (d : I.def_name) =
  let tel, e' = pproc_tel s cG [] is_syntax e in
  let (d', args) = match e' with
    | I.App (I.Const n', ds) -> n', ds
    | I.Const n' -> n', []
    | _ -> raise (Error.Error ("Return type of constructor " ^ n ^ " should be " ^ d))
  in
  if d = d' then
    (add_name_sign s n, (n, tel, (d', args)))
  else
    raise (Error.Error ("Return type of constructor " ^ n ^ " should be " ^ d))

let pproc_sdecl s cG (n, e) (is_syntax : bool) (d : I.def_name) =
  let tel, e' = pproc_stel s cG [] is_syntax e in
  let (d', args) = match e' with
    | I.App (I.Const n', ds) -> n', ds
    | I.Const n' -> n', []
    | _ -> raise (Error.Error ("Return type of constructor " ^ n ^ " should be " ^ d))
  in
  if d = d' then
    (add_name_sign s n, (n, tel, (d', args)))
  else
    raise (Error.Error ("Return type of constructor " ^ n ^ " should be " ^ d))

let pproc_param s cG (is_syntax : bool) (icit, n, e) =
  let cG', n' = add_name_ctx cG n in
  cG', (icit, n', pproc_exp s cG [] is_syntax e)

let rec pproc_pat (s : sign) cG cP p =
  let print_ctx cG = "[" ^ String.concat ", " (List.map (fun (e, i) -> e ^ ", " ^ Name.print_name i) cG) ^ "]" in
  let f pat = pproc_pat s cG cP pat in
  Debug.print (fun () -> "Procesing pattern : " ^ E.print_pat p ^ " with current context " ^ print_ctx cG);
  match p with
  | E.PIdent n -> find_pat_name s cG cP n
  | E.Innac e ->
     Debug.print (fun () -> "Preprocessing inaccessible pattern " ^ E.print_exp e ^ " in context " ^ print_ctx cG);
     cG, I.Innac (pproc_exp s cG [] false e)
  | E.PLam (x, p) ->
    let cG', p' = pproc_pat s cG (add_name_bvars cP x) p in
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
    cG', I.PAnnot (p', pproc_exp s [] [] false t)
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
    cG'', I.PDot (p1', p2')
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

let rec pproc_pats s cG = function
  | [] -> cG, []
  | p :: ps ->
     let cG', p' = pproc_pat s cG [] p in
     let cG'', ps' = pproc_pats s cG' ps in
     cG'', p' :: ps'

let pproc_def_decl s (pats, e) =
  let cG', pats' = pproc_pats s [] pats in
  (pats', I.Just (pproc_exp s cG' [] false e))

let params_to_ctx = List.map2 (fun (_, n, _) (_, n', _) -> n, n')

let pre_process s = function
  | E.Data (n, ps, e, ds) ->
     let _, ps' = List.fold_left (fun (cG, ps) p -> let cG', p' = pproc_param s cG false p in cG', (p'::ps)) ([], []) ps in
     let cG = params_to_ctx ps ps' in
     let is, u = match pproc_tel s cG [] false e with
       | tel, I.Set u -> tel, u
       | _, t -> raise (Error.Error ("Expected universe but instead got expression " ^ I.print_exp t))
     in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s cG d false n in ss, (dd :: dos)) (s', []) ds in
     s'', I.Data (n, ps', is, u, ds')
  | E.Syn (n, e, ds) ->
    let tel, e' = pproc_stel s [] [] true e in
    let _ = match e' with
      | I.Star -> ()
      | _ -> raise (Error.Error ("Syntax definition for " ^ n ^ " should have kind ★ instead of " ^ I.print_exp e'))
    in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_sdecl s [] d true n in ss, (dd :: dos)) (s', []) ds in
     s'', I.Syn (n, tel, ds')
  | E.DefPM (n, e, ds) ->
     let s' = add_name_sign s n in
     let e' = pproc_exp s [] [] false e in
     let lengths = List.map (fun (ps, _) -> List.length ps) ds in
     if try List.for_all ((=) (List.hd lengths)) lengths
        with Failure _ -> raise (Error.Error ("Empty set of patterns for definition " ^ n))
     then () else raise (Error.Error ("Not all pattern spines are of the same length for definition " ^ n));
     begin match e' with
     | I.Pi(tel, e'') ->
        s', I.DefPM (n, tel, e'', List.map (pproc_def_decl s') ds)
     | e'' -> s', I.DefPM (n, [], e'', List.map (pproc_def_decl s') ds)
     end
  | E.Def (n, t, e) ->
     let s' = add_name_sign s n in
     s', I.Def (n, pproc_exp s [] [] false t, pproc_exp s [] [] false e)

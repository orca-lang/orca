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
module EP = Print.Ext
module I = Syntax.Int
module IP = Print.Int

open Location


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
let find_name (sign : sign) (cG : ctx) (cP : bctx) (n, pos : E.name * src_pos) : I.exp =
  match index n cP with
  | Some i -> I.BVar i
  | None -> match lookup n cG with
            | Some n -> I.Var n
            | None ->
               if List.mem n sign
               then I.Const n
               else raise (Error.Error_loc (pos, "Unbound variable: " ^ n))

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

let find_pat_name (s : sign) (cG : ctx) (cP : bctx) (n : E.name) : ctx * E.pat =
    begin
      match index n cP with
      | Some i -> cG, E.PBVar i
      | None ->
        if List.mem n s then
          cG, E.PConst (n, [])
        else
          begin
            match lookup n cG with
            | Some _ -> raise (Error.Error ("Repeated variable " ^ n ^ " in pattern spine"))
            | None ->
              let cG', n' = add_name_ctx cG n in
              cG', E.PVar n'
          end
    end

let rec get_bound_var_ctx (e: E.exp) : bctx =
  match content e with
  | E.Comma (g, P(_, E.Annot(P(_, E.Ident n), _))) -> n :: (get_bound_var_ctx g)
  | E.Annot(P(_, E.Ident n), _) -> [n]
  | E.Nil -> []
  | _ -> []

let rec get_bound_var_ctx_no_annot (e : E.exp) : bctx =
  match content e with
  | E.Comma (g, P(_, E.Annot(P(_, E.Ident n), _))) -> n :: (get_bound_var_ctx_no_annot g)
  | E.Comma (g, P(_, E.Ident n)) -> n :: (get_bound_var_ctx_no_annot g)
  | E.Annot(P(_, E.Ident n), _) -> [n]
  | E.Nil -> []
  | E.Ident _ -> []
  | _ -> raise (Error.Error_loc (loc e, EP.print_exp e ^ " is a forbidden expression on the left hand side of :>"))

let rec get_bound_var_ctx_in_pat (p : E.pat) : bctx =
  match p with
  | E.PComma (g, E.PIdent n) -> n :: (get_bound_var_ctx_in_pat g)
  | E.PNil -> []
  | E.PIdent _ -> []
  | p -> raise (Error.Error (EP.print_pat p ^ " is a forbidden pattern on the left hand side of :>"))

let rec pproc_exp (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : I.exp =
  Debug.print (fun () -> "Preprocessing expression " ^ EP.print_exp e);
  Debug.begin_verbose();
  Debug.indent ();
  let f e = pproc_exp s cG cP e in
  let res = match content e with
  | E.Star -> I.Star
  | E.Set n -> I.Set n
  | E.Ctx -> I.Ctx
  (* | E.Arr (t0, t1) when is_syntax -> *)
  (*   let tel, t' = pproc_stel s cG cP is_syntax e in *)
  (*   I.SPi (tel, t') *)
  | E.SArr (t0, t1) ->
    let tel, t' = pproc_stel s cG cP e in
    I.SPi (tel, t')
  | E.Arr (t0, t1) ->
    let tel, t' = pproc_tel s cG cP e in
     I.Pi (tel, t')
  | E.Box (g, e) ->
    if isEmpty cP then
     let cP' = get_bound_var_ctx g in
     I.Box(pproc_exp s cG cP' g, pproc_exp s cG cP' e)
    else
      raise (Error.Error_loc (loc e, "Bound variables bindings (|-) cannot be nested"))
  | E.TBox (g, e) ->
    if isEmpty cP then
      let cP' = get_bound_var_ctx_no_annot g in
      pproc_exp s cG cP' e
    else
      raise (Error.Error_loc (loc e, "Bound variables bindings (:>) cannot be nested"))
  | E.Fn (ns, e) ->
     let cG', n' = add_names_ctx cG ns in
     I.Fn(n', pproc_exp s cG' cP e)
  | E.Lam (n, e) ->
     I.Lam(n, pproc_exp s cG (add_name_bvars cP n) e)
  | E.App (e1, e2) ->
     let h, sp = pproc_app s cG cP e in
     I.App(h, sp)
  | E.AppL (e1, e2) ->
    let h, sp = pproc_app s cG cP e in
     I.AppL(h, sp)
  | E.Ident n -> find_name s cG cP (n, loc e)
  | E.Clos (e, s) -> I.Clos(f e, f s)
  | E.EmptyS -> I.EmptyS
  | E.Shift n -> I.Shift n
  | E.Semicolon (e1, e2) -> I.Dot(f e1, f e2)
  | E.Comma (e1, e2) ->
    snd (pproc_comma s cG [] e)
  (* | E.Comma (e1, P(_, E.Annot (P(_, E.Ident x), e2))) -> I.Snoc (f e1, x, f e2) *)
  (* | E.Comma (e1, e2) -> I.Snoc (f e1, "_", f e2) *)
  | E.Nil -> I.Nil
  | E.Annot (e1, e2) -> I.Annot(f e1, f e2)
  | E.Hole (Some n) -> I.Hole (Name.gen_name n)
  | E.Hole None -> I.Hole (Name.gen_name "H")
  in Debug.deindent ();
     Debug.end_verbose();
  res

and pproc_comma (s : sign) (cG : ctx) (cP : bctx) (g : E.exp) : bctx * I.exp =
  match content g with
  | E.Ident n ->
    begin match find_name s cG cP (n, loc g) with
    | I.Var n as e -> cP, e
    | e -> raise (Error.Error ("End of a comma expression needs to be a context variable. Instead found: " ^ IP.print_exp e))
    end
  | E.Annot (P(_, E.Ident n), e) ->
    n::cP, I.Snoc(I.Nil, n, pproc_exp s cG cP e)
  | E.Nil -> cP, I.Nil
  | E.Comma(e1, e2) ->
    let cP', e1' = pproc_comma s cG cP e1 in
    begin match content e2 with
    | E.Annot (P(_, E.Ident n), e) ->
      n::cP', I.Snoc(e1', n, pproc_exp s cG cP' e)
    | _ -> "_"::cP', I.Snoc(e1', "_", pproc_exp s cG cP' e2)
    end
  | _ -> raise (Error.Error_loc (loc g, "Left hand side of comma should be a context. Instead found: " ^ EP.print_exp g))

and pproc_tel (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : I.tel * I.exp =
  let rec g cG e t0 = match content e with
    | E.App (P(_, E.Ident n), e') ->
      let cG', n' = add_name_ctx cG n in
      let cG'', tel = g cG' e' t0 in
      cG'', (Syntax.Explicit, n', t0) :: tel
    | E.Ident n ->
      let cG'', n' = add_name_ctx cG n in
      cG'', [Syntax.Explicit, n', t0]
    | _ -> raise (Error.Error_loc (loc e, "Left hand side of arrow was not a series of identifiers annotated by a type."))
  in
  let rec f cG e = match content e with
    | E.Annot (e, t0) ->
      let t0' = pproc_exp s cG cP t0 in
      let cG', tel = g cG e t0' in
      Debug.print ~verbose:true (fun () -> "Calling f in pproc_tel\ntel = " ^ IP.print_tel tel);
      cG', tel
    | E.App (P(_, E.Annot(e, t0)), t1) ->
      let t0' = pproc_exp s cG cP t0 in
      let cG', tel = g cG e t0' in
      let cG'', tel'  = f cG' t1 in
      Debug.print ~verbose:true (fun () -> "Calling f in pproc_tel\ntel = " ^ IP.print_tel tel ^ "\ntel' = " ^ IP.print_tel tel');
      cG'', tel @ tel'
    | _ -> let tel = [Syntax.Explicit, Name.gen_floating_name (), pproc_exp s cG cP e] in
           Debug.print ~verbose:true (fun () -> "Calling f in pproc_tel. Fall through, resulting in = " ^ IP.print_tel tel);
      cG, tel
  in
  match content e with
  | E.Arr (t0, t1) ->
    let cG', tel = f cG t0 in
    let tel', t = pproc_tel s cG' cP t1 in
     tel @ tel' , t
  | _ -> Debug.print ~verbose:true (fun () -> "preproc tel matched against " ^ EP.print_exp e);
    [], pproc_exp s cG cP e

and pproc_stel (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : I.stel * I.exp =
  match content e with
  | E.Arr (P(_, E.Annot (P(_, E.Ident n), t0)), t1)
  | E.SArr (P(_, E.Annot (P(_, E.Ident n), t0)), t1) ->
     let cP' = add_name_bvars cP [n] in
     let tel, t = pproc_stel s cG cP' t1 in
     (Syntax.Explicit, n, pproc_exp s cG cP t0) :: tel, t
  | E.Arr (t0, t1)
  | E.SArr (t0, t1) ->
    let cP' = add_name_bvars cP ["_"] in
     let tel, t = pproc_stel s cG cP' t1 in
     (Syntax.Explicit, "_", pproc_exp s cG cP t0) :: tel , t
  | t -> [], pproc_exp s cG cP (ghost t)

and pproc_app (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : I.exp * I.exp list =
  match content e with
  | E.App(e1, e2) ->
     let h, sp = pproc_app s cG cP e1 in
     h, sp @[pproc_exp s cG cP e2]
  | E.AppL(e1, e2) ->
     let h, sp = pproc_app s cG cP e1 in
     h, sp @[pproc_exp s cG cP e2]
  | _ -> pproc_exp s cG cP e, []

let pproc_decl s cG (n, e) (d : I.def_name) =
  Debug.print (fun () -> "Preprocessing declaration " ^ n ^ "\nCreating telescope out of " ^ EP.print_exp e);
  Debug.indent ();
  let tel, e' = pproc_tel s cG [] e in
  let (d', args) = match e' with
    | I.App (I.Const n', ds) -> n', ds
    | I.Const n' -> n', []
    | _ -> raise (Error.Error_loc (loc e, "Return type of constructor " ^ n ^ " should be " ^ d))
  in
  Debug.deindent ();
  if d = d' then
    (add_name_sign s n, (n, tel, (d', args)))
  else
    raise (Error.Error_loc (loc e, "Return type of constructor " ^ n ^ " should be " ^ d))

let pproc_sdecl s cG (n, e) (is_syntax : bool) (d : I.def_name) =
  let tel, e' = pproc_stel s cG [] e in
  let (d', args) = match e' with
    | I.App (I.Const n', ds) -> n', ds
    | I.Const n' -> n', []
    | _ -> raise (Error.Error_loc (loc e, "Return type of constructor " ^ n ^ " should be " ^ d))
  in
  if d = d' then
    (add_name_sign s n, (n, tel, (d', args)))
  else
    raise (Error.Error_loc (loc e, "Return type of constructor " ^ n ^ " should be " ^ d))

let pproc_param s cG (icit, n, e) =
  let cG', n' = add_name_ctx cG n in
  cG', (icit, n', pproc_exp s cG [] e)

let rec collect_pat_vars (s : sign) cG cP p =
  match p with
  | E.PIdent n -> find_pat_name s cG cP n
  | E.Innac e -> cG, E.Innac e
  | E.PLam (x, p) ->
    let cG', p' = collect_pat_vars s cG (add_name_bvars cP x) p in
    cG', E.PLam (x,  p')
  | E.PConst (c, ps) ->
    let g (cG, ps) p =
      let cG', p' = collect_pat_vars s cG cP p in
      cG', p' :: ps
    in
    let cG', ps' = List.fold_left g (cG, []) ps in
    cG', E.PConst (c, List.rev ps')
  | E.PClos (x, e) ->
    begin match find_pat_name s cG cP x with
    | cG', E.PVar n ->
      cG', E.PClos' (n, e)
    | cG', _ -> raise (Error.Error "Substitution can only be applied to pattern variables")
    end
  | E.PEmptyS -> cG, E.PEmptyS
  | E.PShift i -> cG, E.PShift i
  | E.PDot (p1, p2) ->
    let cG', p1' = collect_pat_vars s cG cP p1 in
    let cG'', p2' = collect_pat_vars s cG' cP p2 in
    cG'', E.PDot (p1', p2')
  | E.PNil -> cG, E.PNil
  | E.PComma (p1, p2) -> assert false
  | E.PBox (g, p) ->
    if isEmpty cP then
      let cP' = get_bound_var_ctx_in_pat g in
      collect_pat_vars s cG cP' p
    else
      raise (Error.Error "Bound variables bindings (:>) cannot be nested")
  | E.PPar n ->
    begin match find_pat_name s cG cP n with
    | cG', E.PVar n' -> cG', E.PPar' n'
    | _ -> raise (Error.Error (n ^ " was marked as parameter variable but was identified to be something else"))
    end
    | E.PUnder -> cG, E.PUnder
  | E.PWildcard -> cG, E.PWildcard
  | _ -> raise (Error.Violation ("Found temporary constructors that can only be created by this function"))


let rec pproc_pat (s : sign) cG cP p =
  let print_ctx cG = "[" ^ String.concat ", " (List.map (fun (e, i) -> e ^ ", " ^ Name.print_name i) cG) ^ "]" in
  let f pat = pproc_pat s cG cP pat in
  Debug.print (fun () -> "Procesing pattern : " ^ EP.print_pat p ^ " with current context " ^ print_ctx cG);
  match p with
  | E.PIdent _ -> raise (Error.Violation "Found PIdent on second pass")
  | E.PPar _ -> raise (Error.Violation "Found PPar on second pass")
  | E.PClos _ ->  raise (Error.Violation "Found PClos on second pass")
  | E.PPar' n -> I.PPar n
  | E.PVar n -> I.PVar n
  | E.PBVar i -> I.PBVar i
  | E.Innac e ->
     Debug.print (fun () -> "Preprocessing inaccessible pattern " ^ EP.print_exp e ^ " in context " ^ print_ctx cG);
     I.Innac (pproc_exp s cG [] e)
  | E.PLam (x, p) ->
    I.PLam (x, pproc_pat s cG (add_name_bvars cP x) p)
  | E.PConst (c, ps) ->
    let ps' = List.map (pproc_pat s cG cP) ps in
    I.PConst (c, ps')
  | E.PClos' (x, e) ->
    let rec pat_subst_of_exp = function
      | E.EmptyS -> I.CEmpty
      | E.Shift n -> I.CShift n
      | E.Semicolon (sigma, P(_,E.Ident n)) ->
        let i = match find_pat_name s cG cP n with
          | _, E.PBVar i -> i
          | _ -> raise (Error.Error ("Substitution in pattern can only contain bound variables"))
        in I.CDot (pat_subst_of_exp (content sigma), i)
      | e -> raise (Error.Error ("Expected pattern substitution."))
    in
    I.PClos (x, pat_subst_of_exp (content e))
  | E.PEmptyS -> I.PEmptyS
  | E.PShift i -> I.PShift i
  | E.PDot (p1, p2) ->
    I.PDot (f p1, f p2)
  | E.PNil -> I.PNil
  | E.PComma (p1, p2) -> assert false
  | E.PBox (g, p) ->
    if isEmpty cP then
      let cP' = get_bound_var_ctx_in_pat g in
      pproc_pat s cG cP' p
    else
      raise (Error.Error "Bound variables bindings (:>) cannot be nested")
  | E.PUnder -> I.PUnder
  | E.PWildcard -> I.PWildcard

let rec pproc_pats s cG = function
  | [] -> []
  | p :: ps ->
    pproc_pat s cG [] p :: pproc_pats s cG ps

let rec collect_pats_vars s cG = function
  | [] -> cG, []
  | p :: ps ->
     let cG', p' = collect_pat_vars s cG [] p in
     let cG'', ps' = collect_pats_vars s cG' ps in
     cG'', p' :: ps'

let pproc_def_decl s (pats, e) =
  let cG, pats' = collect_pats_vars s [] pats in
  let pats'' = pproc_pats s cG pats' in
  (pats'', I.Just (pproc_exp s cG [] e))

let params_to_ctx = List.map2 (fun (_, n, _) (_, n', _) -> n, n')

let pre_process s = function
  | E.Data (n, ps, e, ds) ->
    Debug.print (fun () -> "Preprocessing datatype : " ^ n ^ "\nps = " ^ EP.print_params ps);
    let rec fold_param cG ps =
      match ps with
      | p :: ps ->
        let cG', p' = pproc_param s cG p in
        let cG'', ps' = fold_param cG' ps in
        cG'', p' :: ps'
      | [] -> cG, []
    in
    let cGa, ps' = fold_param [] ps in
    Debug.print ~verbose:true (fun () -> "ps' = " ^ IP.print_tel ps');
     let cG = params_to_ctx ps ps' in
     let is, u = match pproc_tel s cG [] e with
       | tel, I.Set u -> tel, u
       | _, t -> raise (Error.Error_loc (loc e, "Expected universe but instead got expression " ^ IP.print_exp t))
     in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s cG d n in ss, (dd :: dos)) (s', []) ds in
     s'', I.Data (n, ps', is, u, ds')
  | E.Syn (n, e, ds) ->
    let tel, e' = pproc_tel s [] [] e in
    let _ = match e' with
      | I.Star -> ()
      | _ -> raise (Error.Error_loc (loc e, "Syntax definition for " ^ n ^ " should have kind * instead of " ^ IP.print_exp e'))
    in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s [] d n in ss, (dd :: dos)) (s', []) ds in
     s'', I.Syn (n, tel, ds')
  | E.DefPM (n, e, ds) ->
     let s' = add_name_sign s n in
     let e' = pproc_exp s [] [] e in
     let lengths = List.map (fun (ps, _) -> List.length ps) ds in
     if try List.for_all ((=) (List.hd lengths)) lengths
        with Failure _ -> raise (Error.Error ("Empty set of patterns for definition " ^ n))
     then () else raise (Error.Error_loc (loc e, "Not all pattern spines are of the same length for definition " ^ n));
     begin match e' with
     | I.Pi(tel, e'') ->
        s', I.DefPM (n, tel, e'', List.map (pproc_def_decl s') ds)
     | e'' -> s', I.DefPM (n, [], e'', List.map (pproc_def_decl s') ds)
     end
  | E.Def (n, t, e) ->
     let s' = add_name_sign s n in
     s', I.Def (n, pproc_exp s [] [] t, pproc_exp s [] [] e)

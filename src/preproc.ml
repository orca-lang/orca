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

open Syntax
module E = Syntax.Ext
module EP = Print.Ext
module A = Syntax.Apx
module AP = Print.Apx

open Loc

type sign = E.name list (* The signature for types *)
type ctx = (E.name * Name.name) list  (* The context for regular variables *)
type bctx = (E.name list) list            (* The context for bound variables *)

let rec print_bctx =
  let print_block ns = "| " ^  String.concat ", " ns ^ " |" in
  function
  | [] -> ""
  | [n]::xs -> n ^ ", " ^ print_bctx xs
  | ns::xs -> print_block ns

let add_name_bvars cP ns : bctx = (List.map (fun n -> [n]) ns) @ cP

let rec lookup cG n =
  match cG with
  | (n', nn) :: _ when n = n' -> Some nn
  | _ :: xs -> lookup xs n
  | [] -> None

let index n cP =
  let rec proj n i = function
    | [n'] when i = 0 && n = n' -> Some None
    | n' :: _ when n = n' -> Some (Some i)
    | _ :: xs -> proj n (i + 1) xs
    | [] -> None
  in
  let rec index n i = function
    | x :: xs ->
       begin match proj n 0 x with
       | None -> index n (i + 1) xs
       | Some p -> Some (i, p)
       end
    | [] -> None
  in
  index n 0 cP

(* Finds a name in the signature or the context and returns the
   appropriate internal expression *)
let find_name (sign : sign) (cG : ctx) (cP : bctx) (n, pos : E.name * src_pos) : A.exp =
  Debug.print(fun () -> "Fooooooo cP = " ^ (String.concat ", " (List.map (fun x -> "[" ^ (String.concat "," x) ^ "]") cP))) ;
  match index n cP with
  | Some i -> A.BVar i
  | None -> match lookup cG n with
            | Some n -> A.Var n
            | None ->
               if List.mem n sign
               then A.Const n
               else raise (Error.Error_loc (pos, "Unbound variable: " ^ n))

let lookup_bound_name x cP =
  let rec lookup i cP =
    match cP with
    | (_,x')::cP' when x = x' -> i
    | _::cP' -> lookup (i+1) cP'
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup 0 cP

let find_name_pat (sign : sign) (cG : ctx) (cP : bctx) (n : E.name) : A.pat =
  match index n cP with
  | Some i -> A.PBVar i
  | None -> match lookup cG n with
            | Some n -> A.PVar n
            | None ->
               if List.mem n sign
               then A.PConst (n , [])
               else raise (Error.Error ("Unbound variable: " ^ n))

let add_names_sign sign ns = ns @ sign
let add_name_sign sign n = n :: sign
let add_name_ctx c n = let nn = Name.gen_name n in ((n, nn) :: c), nn
let rec add_names_ctx c = function
  | [] -> c, []
  | n::ns ->
     let c', n' = add_name_ctx c n in
     let c'', ns' = add_names_ctx c' ns in
     c'', n'::ns'

let collect_pat_ctx (s : sign) (cG : ctx) (cP : bctx) (n : E.name) : ctx =
    begin
      match index n cP with
      | Some i -> cG
      | None ->
        if List.mem n s then
          cG
        else
          begin
            match lookup cG n with
            | Some _ -> raise (Error.Error ("Repeated variable " ^ n ^ " in pattern spine"))
            | None -> fst(add_name_ctx cG n)
          end
    end

let rec get_bound_var_ctx (e: E.exp) : bctx =
  match content e with
  | E.Comma (g, P(_, E.Annot(P(_, E.Ident n), _))) -> [n] :: (get_bound_var_ctx g)
  | E.Annot(P(_, E.Ident n), _) -> [[n]]
  | E.Nil -> []
  | _ -> []

let rec get_bound_var_ctx_no_annot (e : E.exp) : bctx =
  match content e with
  | E.Comma (g, P(_, E.Annot(P(_, E.Ident n), _))) ->
     [n] :: (get_bound_var_ctx_no_annot g)
  | E.Comma (g, P(_, E.Ident n)) ->
     [n] :: (get_bound_var_ctx_no_annot g)
  | E.Comma (g, P(_, E.Block l)) ->
     let f = function
       |  (_, P(_, E.Ident n)) -> n
       | _ -> raise (Error.Error ("Block in left-hand side of :> should only be identifiers"))
     in
     List.map f (Rlist.to_list l) :: get_bound_var_ctx_no_annot g
  | E.Annot(P(_, E.Ident n), _) ->
     [[n]]

  | E.Nil -> []
  | E.Ident _ -> []
  | _ -> raise (Error.Error_loc (loc e, EP.print_exp e ^ " is a forbidden expression on the left hand side of :>"))

let rec get_bound_var_ctx_in_pat (p : E.pat) : bctx =
  match p with
  | E.PComma (g, Some n, _) -> [n] :: (get_bound_var_ctx_in_pat g)
  | E.PCommaBlock (g, ns) -> ns :: (get_bound_var_ctx_in_pat g)
  | E.PNil -> []
  | E.PIdent _ -> []            (* MMMM *)
  | p -> raise (Error.Error (EP.print_pat p ^ " is a forbidden pattern on the left hand side of :>"))

let rec pproc_exp (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : A.exp =
  Debug.print (fun () -> "Preprocessing expression " ^ EP.print_exp e);
  Debug.indent ();
  let f e = pproc_exp s cG cP e in
  let res =
match content e with
  | E.Star -> A.Star
  | E.Set n -> A.Set n
  | E.Ctx sch -> A.Ctx (pproc_schema s cG cP sch)

  (* | E.Arr (t0, t1) when is_syntax -> *)
  (*   let tel, t' = pproc_stel s cG cP is_syntax e in *)
  (*   I.SPi (tel, t') *)
  | E.SArr (t0, t1) ->
    let tel, t' = pproc_stel s cG cP e in
    A.SPi (tel, t')
  | E.Arr (t0, t1) ->
    let tel, t' = pproc_tel s cG cP e in
     A.Pi (tel, t')
  | E.Box (g, e) ->
    if cP = [] then
     let cP' = get_bound_var_ctx g in
     A.Box(pproc_exp s cG cP' g, pproc_exp s cG cP' e)
    else
      raise (Error.Error_loc (loc e, "Bound variables bindings (|-) cannot be nested"))
  | E.ABox (g, e) ->
     let cP' = get_bound_var_ctx_no_annot g in
     Debug.print (fun () -> " Fooooooo cP = " ^ (String.concat ", " (List.map (fun x -> "[" ^ (String.concat "," x) ^ "]") cP))) ;
     pproc_exp s cG cP' e

  | E.Fn (ns, e) ->
     let cG', n' = add_names_ctx cG ns in
     A.Fn(n', pproc_exp s cG' cP e)
  | E.Lam (ns, e) ->
    let rec accumulate_lams e = match content e with
    | E.Lam (ns, e) -> 
      let ns', e' = accumulate_lams e in
      ns @ ns', e'
    | _ -> [], e
    in 
    let ns', e' = accumulate_lams e in
    let ns'' = ns @ ns' in
     A.Lam(ns'', pproc_exp s cG (add_name_bvars cP ns'') e')
  | E.App (e1, e2) ->
     let h, sp = pproc_app s cG cP e in
     A.App(h, sp)
  | E.AppL (e1, e2) ->
    let h, sp = pproc_app s cG cP e in
     A.AppL(h, sp)
  | E.Ident n -> find_name s cG cP (n, loc e)
  | E.BVar i -> A.BVar (i, None)
  | E.Clos (e, P(_, E.Shift 0)) -> A.Clos(f e, A.Shift 0)
  | E.Clos (e1, e2) ->
     let e1' = try
         pproc_exp s cG [] e1
       with Error.Error msg ->
         raise (Error.Error ("While indexing on the left of " ^ EP.print_exp e
                             ^ "\n Faild with: " ^  msg))
     in
     A.Clos(e1' , f e2)
  | E.Empty -> A.Empty
  | E.Shift n -> A.Shift n
  | E.Semicolon (e1, P(_, E.Block l)) ->
     let l' = Rlist.map (fun (_, e) -> pproc_exp s cG cP e) l in
     A.Dot(f e1, A.TBlock l')
  | E.Semicolon (e1, e2) -> A.Dot(f e1, f e2)
  | E.Comma (e1, e2) ->
    snd (pproc_comma s cG [] e)
  | E.Nil -> A.Nil
  | E.Annot (e1, e2) -> A.Annot(f e1, f e2)
  | E.Hole (Some n) -> A.Hole (Name.gen_name n)
  | E.Hole None -> A.Hole (Name.gen_name "H")
  | E.Block bs ->
     let bs' = pproc_block s cG cP bs in
     A.Block bs'
  in Debug.deindent ();
  res

and pproc_block (s : sign) (cG : ctx) (cP : bctx) (bs : (E.name * E.exp) Rlist.rlist) : (string * A.exp) Rlist.rlist =
  let open Rlist in
  let rec pproc_block' = function
    | RNil -> RNil, cP
    | RCons (bs, (n, e)) ->
      let bs', cP' = pproc_block' bs in
      Debug.print (fun () -> "n = " ^ n ^ " cP = " ^ print_bctx cP' );
      (RCons(bs', (n, pproc_exp s cG cP' e)), [n]::cP')
  in
  let bs', _ = pproc_block' bs in
  bs'

and pproc_schema (s : sign) (cG : ctx) (cP : bctx) (E.Schema (quant, block) : E.schema) : A.schema =
  let rec pproc_part cP = function
    | [] -> [], cP
    | (x, t)::params ->
       let cP' = [x]::cP in
       let params', cP'' = pproc_part cP' params in
       (x, pproc_exp s cG cP t)::params',  cP''   
  in
  let quant', cP' = pproc_part cP quant in 
  let block', _ = pproc_part cP' block in
  A.Schema (quant', block')

and pproc_comma (s : sign) (cG : ctx) (cP : bctx) (g : E.exp) : bctx * A.exp =
  match content g with
  | E.Ident n ->
    begin match find_name s cG cP (n, loc g) with
    | A.Var n as e -> cP, e
    | e -> raise (Error.Error ("End of a comma expression needs to be a context variable. Instead found: " ^ AP.print_exp e))
    end
  | E.Annot (P(_, E.Ident n), e) ->
     [n]::cP, A.Snoc(A.Nil, n, pproc_exp s cG cP e)
  | E.Nil -> cP, A.Nil
  | E.Comma(e1, e2) ->
    let cP', e1' = pproc_comma s cG cP e1 in
    begin match content e2 with
    | E.Annot (P(_, E.Ident n), e) ->
       [n]::cP', A.Snoc(e1', n, pproc_exp s cG cP' e)
    | _ ->
       cP', A.Snoc(e1', Name.gen_string "_", pproc_exp s cG cP' e2)
    end
  | _ -> raise (Error.Error_loc (loc g, "Left hand side of comma should be a context. Instead found: " ^ EP.print_exp g))

and pproc_tel (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : A.tel * A.exp =
  (* f and g are respectively here to allow types of the form
     (a : A) (b : B) -> ... and (a1 a2 : A) -> ... rather than
     (a : A) -> (b : B) -> ... and (a1 : A) -> (a2 : A) -> ... *)
  let g cG e t0 =
    let rec extract_names ns = match content ns with
      | E.Ident n -> [n]
      | E.App (ns, P(_, E.Ident n)) -> n :: extract_names ns
      | _ -> raise (Error.Error "Malformed arrow type")
    in
    let ns = extract_names e in
    let cG', ns' = add_names_ctx cG ns in
    cG', List.map (fun n -> Syntax.Explicit, n, t0) (List.rev ns')
  in
  let rec f cG e = match content e with
    | E.Annot (e, t0) ->
      let t0' = pproc_exp s cG cP t0 in
      let cG', tel = g cG e t0' in
      Debug.print ~verbose:true (fun () -> "Calling f in pproc_tel\ntel = " ^ AP.print_tel tel);
      cG', tel
    | E.App (t0, P(_, E.Annot(e, t1))) ->
      let cG', tel = f cG t0 in
      let t1' = pproc_exp s cG' cP t1 in
      let cG'', tel' = g cG' e t1' in
      Debug.print ~verbose:true (fun () -> "Calling f in pproc_tel\ntel = " ^ AP.print_tel tel ^ "\ntel' = " ^ AP.print_tel tel');
      cG'', tel @ tel'
    | _ -> raise (Error.Error "List of variable declarations was malformed")
  in
  match content e with
  | E.Arr (P(_, E.Annot _) as t0, t1)
  | E.Arr (P(_, E.App (_, P(_, E.Annot _))) as t0, t1) ->
    let cG', tel = f cG t0 in
    let tel', t = pproc_tel s cG' cP t1 in
    tel @ tel' , t
  | E.Arr (t0, t1) ->
    let tel, t = pproc_tel s cG cP t1 in
    (Syntax.Explicit, Name.gen_floating_name (), pproc_exp s cG cP t0) :: tel, t
  | _ -> Debug.print ~verbose:true (fun () -> "preproc tel matched against " ^ EP.print_exp e);
    [], pproc_exp s cG cP e

and pproc_stel (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : A.stel * A.exp =
  (* Just like in pproc_tel, f and g allow for a more condensed of pi types *)
  let g cP e t0 = (* e should be a list of identifiers *)
    let rec extract_names ns = match content ns with
      | E.Ident n -> [n, pproc_exp s cG cP t0]
      | E.App (ns, P(_, E.Ident n)) ->
        let ns' = extract_names ns in
        let cP' = add_name_bvars cP (List.map fst ns') in
        (n, pproc_exp s cG cP' t0) :: ns'
      | _ -> raise (Error.Error "Malformed arrow type")
    in
    (* Note: extract_names is not very nice. We preprocess t0 a number
       of times equal to the number of identifiers in e. This is
       because each new identifier has a type that depends on the
       previous ones. Since everything is handled with DeBruijn
       indices, we need to make sure the numbers are correct each
       time. A more efficient solution could be to apply a shifting
       traversal (or maybe just the term _[^1]?) successively. *)
    let ns' = extract_names e in
    add_name_bvars cP (List.map fst ns'), List.map (fun (n, t0) -> Syntax.Explicit, n, t0) (List.rev ns')
  in
  let rec f cP e = match content e with
    | E.Annot (e, t0) ->
      g cP e t0
    | E.App (t0, P(_, E.Annot(e, t1))) ->
      let cP', tel = f cP t0 in
      let cP'', tel' = g cP' e t1 in
      cP'', tel @ tel'
    | _ -> raise (Error.Error "List of variable declarations was malformed")
  in
  match content e with
  | E.Arr (P(_, E.Annot _) as t0, t1)
  | E.Arr (P(_, E.App (_, P(_, E.Annot _))) as t0, t1)
  | E.SArr (P(_, E.Annot _) as t0, t1)
  | E.SArr (P(_, E.App (_, P(_, E.Annot _))) as t0, t1) ->
    let cP', tel = f cP t0 in
    let tel', t = pproc_stel s cG cP' t1 in
    tel @ tel', t
  | E.Arr (t0, t1)
  | E.SArr (t0, t1) ->
     let tel, t = pproc_stel s cG ([Name.gen_string "_y"]::cP) t1 in
     (Syntax.Explicit, Name.gen_string "_x", pproc_exp s cG cP t0) :: tel , t
  | t -> [], pproc_exp s cG cP (ghost t)

and pproc_app (s : sign) (cG : ctx) (cP : bctx) (e : E.exp) : A.exp * A.exp list =
  match content e with
  | E.App(e1, e2) ->
     let h, sp = pproc_app s cG cP e1 in
     h, sp @[pproc_exp s cG cP e2]
  | E.AppL(e1, e2) ->
     let h, sp = pproc_app s cG cP e1 in
     h, sp @[pproc_exp s cG cP e2]
  | _ -> pproc_exp s cG cP e, []

let pproc_decl s cG (n, e) (d : def_name) =
  Debug.print (fun () -> "Preprocessing declaration " ^ n
                         ^ "\nCreating telescope out of " ^ EP.print_exp e);
  Debug.indent ();
  let tel, e' = pproc_tel s cG [] e in
  let (d', args) = match e' with
    | A.App (A.Const n', ds) -> n', ds
    | A.Const n' -> n', []
    | _ -> raise (Error.Error_loc (loc e, "Return type of constructor " ^ n ^ " should be " ^ d))
  in
  Debug.deindent ();
  if d = d' then
    (add_name_sign s n, (n, tel, (d', args)))
  else
    raise (Error.Error_loc (loc e, "Return type of constructor " ^ n ^ " should be " ^ d))

let pproc_codecl s cG (n, e) (d : def_name) =
  Debug.print (fun () -> "Preprocessing declaration " ^ n
                         ^ "\nCreating telescope out of " ^ EP.print_exp e);
  Debug.indent ();
  let tel, e' = pproc_tel s cG [] e in
  let rec split_cotel acc = function
    | [] -> raise (Error.Error ("Invalid observation declaration for " ^ n ^ ". It needs to eliminate " ^ d))
    | (_, m, A.Const n) :: tel when n = d ->
      List.rev acc, (m, n, []), tel
    | (_, m, A.App (A.Const n, ds)) :: tel when n = d ->
      List.rev acc, (m, n, ds), tel
    | (Explicit, m, t) :: tel when Name.is_name_floating m ->
      raise (Error.Error ("Observation " ^ n ^ " expected arrow type argument before codata term."))
    | t :: tel -> split_cotel (t :: acc) tel
  in
  let tel0, dsig, tel1 = split_cotel [] tel in
  (add_name_sign s n, (n, tel0, dsig, A.Pi (tel1, e')))


let pproc_sdecl s cG (n, e) (d : def_name) =
  let tel, e' = pproc_stel s cG [] e in
  let (d', args) = match e' with
    | A.App (A.Const n', ds) -> n', ds
    | A.Const n' -> n', []
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
  | E.PIdent n -> collect_pat_ctx s cG cP n
  | E.Inacc e -> cG
  | E.PLam (xs, p) ->
     collect_pat_vars s cG ((List.map (fun x -> [x]) xs)@cP) p
  | E.PConst (c, ps) ->
    List.fold_left (fun cG p -> collect_pat_vars s cG cP p) cG ps
  | E.PClos (x, e) -> collect_pat_ctx s cG cP x
  | E.PEmpty -> cG
  | E.PShift i -> cG
  | E.PDot (p1, p2) ->
    let cG' = collect_pat_vars s cG cP p1 in
    collect_pat_vars s cG' cP p2
  | E.PNil -> cG
  | E.PComma (p1, _, p2) ->
     let cG' = collect_pat_vars s cG [] p1 in
     let cP' = get_bound_var_ctx_in_pat p1 in
     collect_pat_vars s cG' cP' p2
  | E.PBox (g, p) ->
      let cP' = get_bound_var_ctx_in_pat g in
      collect_pat_vars s cG cP' p
  | E.PPar (n, _) -> collect_pat_ctx s cG cP n
  | E.PUnder -> cG
  | E.PWildcard -> cG

let rec pproc_pat (s : sign) cG cP p =
  let print_ctx cG = "[" ^ String.concat ", " (List.map (fun (e, i) -> e ^ ", " ^ Name.print_name i) cG) ^ "]" in
  let f pat = pproc_pat s cG cP pat in
  Debug.print (fun () -> "Procesing pattern : " ^ EP.print_pat p ^ " with current context " ^ print_ctx cG);
  match p with
  | E.PIdent n -> find_name_pat s cG cP n
  | E.PPar (n, pr) ->
     begin match find_name_pat s cG cP n with
     | A.PVar n -> A.PPar (n, pr)
     | _ -> raise (Error.Error "Expected parameter variable, got something else")
     end
  | E.PClos (x, e) ->
    let rec pat_subst_of_exp = function
      | E.Empty -> CEmpty
      | E.Shift n -> CShift n
      | E.Semicolon (sigma, P(_,E.Ident n)) ->
        let n' = match find_name_pat s cG cP n with
          | A.PBVar n' -> n'
          | _ -> raise (Error.Error ("Substitution in pattern can only contain bound variables"))
        in CDot (pat_subst_of_exp (content sigma), n')
      | e -> raise (Error.Error ("Expected pattern substitution."))
    in
    let x' = match find_name_pat s cG cP x with
      | A.PVar n -> n
      | _ -> raise (Error.Error ("Closures in patterns can only be applied to meta variables"))
    in
    A.PClos (x', pat_subst_of_exp (content e))
  | E.Inacc e ->
     Debug.print (fun () -> "Preprocessing inaccessible pattern " ^ EP.print_exp e ^ " in context " ^ print_ctx cG);
     A.Inacc (pproc_exp s cG [] e)
  | E.PLam (xs, p) ->
    let rec accumulate_plams = function
    | E.PLam (xs, p) -> 
      let xs', p' = accumulate_plams p in
      xs @ xs', p'
    | p -> [], p
    in 
    let xs', p' = accumulate_plams p in
    let xs'' = xs @ xs' in
    A.PLam (xs, pproc_pat s cG ((List.map (fun x -> [x]) xs'')@cP) p')
  | E.PConst (c, ps) ->
    let ps' = List.map (pproc_pat s cG cP) ps in
    A.PConst (c, ps')
  | E.PEmpty -> A.PEmpty
  | E.PShift i -> A.PShift i
  | E.PDot (p1, p2) ->
    A.PDot (f p1, f p2)
  | E.PNil -> A.PNil
  | E.PComma (p1, x, p2) ->
     let x = match x with
       | None -> "_2vf23"
       | Some x -> x
     in
     Debug.print(fun () -> "Preprocessing comma\np1 = " ^ EP.print_pat p1 ^ "\np2 = " ^ EP.print_pat p2);
     let p1' = pproc_pat s cG [] p1 in
     let p2' = pproc_pat s cG (get_bound_var_ctx_in_pat p1) p2 in
     Debug.print(fun () -> "resulting in \np1' = " ^ AP.print_pat p1' ^ "\np2' = " ^ AP.print_pat p2');
     A.PSnoc(p1', x, p2')
  | E.PBox (g, p) ->
      let cP' = get_bound_var_ctx_in_pat g in
      pproc_pat s cG cP' p
  | E.PUnder -> A.PUnder
  | E.PWildcard -> A.PWildcard

let rec pproc_pats s cG = function
  | [] -> []
  | p :: ps ->
    pproc_pat s cG [] p :: pproc_pats s cG ps

let rec collect_pats_vars s cG = function
  | [] -> cG
  | p :: ps ->
     let cG' = collect_pat_vars s cG [] p in
     collect_pats_vars s cG' ps

let pproc_def_decl s (pats, e) =
  let cG = collect_pats_vars s [] pats in
  let pats' = pproc_pats s cG pats in
  (pats', A.Just (pproc_exp s cG [] e))

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
    Debug.print ~verbose:true (fun () -> "ps' = " ^ AP.print_tel ps');
     let cG = params_to_ctx ps ps' in
     let is, u = match pproc_tel s cG [] e with
       | tel, A.Set u -> tel, u
       | _, t -> raise (Error.Error_loc (loc e, "Expected universe but instead got expression " ^ AP.print_exp t))
     in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_decl s cG d n in ss, (dd :: dos)) (s', []) ds in
     s'', A.Data (n, ps', is, u, ds')
  | E.Codata (n, ps, e, ds) ->
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
    Debug.print ~verbose:true (fun () -> "ps' = " ^ AP.print_tel ps');
     let cG = params_to_ctx ps ps' in
     let is, u = match pproc_tel s cG [] e with
       | tel, A.Set u -> tel, u
       | _, t -> raise (Error.Error_loc (loc e, "Expected universe but instead got expression " ^ AP.print_exp t))
     in
     let s' = add_name_sign s n in
     let s'', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_codecl s cG d n in ss, (dd :: dos)) (s', []) ds in
     s'', A.Codata (n, ps', is, u, ds')
  | E.Spec spec ->
    let ns = List.map (fun (n, _, _) -> n) spec in
    let s' = add_names_sign s ns in
    let rec process s = function
      | (n, e, ds) :: spec ->
        let tel, e' = pproc_stel s [] [] e in
        let _ = match e' with
          | A.Star -> ()
          | _ -> raise (Error.Error_loc (loc e, "Syntax definition for " ^ n ^ " should have kind * instead of " ^ AP.print_exp e'))
        in
        let s', ds' = List.fold_left (fun (s, dos) d -> let ss, dd = pproc_sdecl s [] d n in ss, (dd :: dos)) (s, []) ds in
        let s'', spec' = process s' spec in
        s'', (n, tel, ds') :: spec'
      | [] -> s, []
    in
    let s'', spec' = process s' spec in
    s'', A.Spec spec'
  | E.DefPM def ->
    let ns = List.map (fun (n, _, _) -> n) def in
    let s' = add_names_sign s ns in
    let rec process = function
      | (n, e, ds) :: def ->
        let e' = pproc_exp s [] [] e in
        let lengths = List.map (fun (ps, _) -> List.length ps) ds in
        if begin
          try List.for_all ((=) (List.hd lengths)) lengths
          with Failure _ -> raise (Error.Error ("Empty set of patterns for definition " ^ n))
        end
        then () else raise (Error.Error_loc (loc e, "Not all pattern spines are of the same length for definition " ^ n));
        begin match e' with
        | A.Pi(tel, e'') -> (n, tel, e'', List.map (pproc_def_decl s') ds) :: process def
        | e'' -> (n, [], e'', List.map (pproc_def_decl s') ds) :: process def
        end
      | [] -> []
    in
    s', A.DefPM (process def)

  | E.Def (n, t, e) ->
     let s' = add_name_sign s n in
     s', A.Def (n, pproc_exp s [] [] t, pproc_exp s [] [] e)

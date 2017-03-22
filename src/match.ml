open Syntax
open Print
open Sign
open Recon
open Name
open Procpat

module A = Syntax.Apx
module AP = Print.Apx
module I = Syntax.Int
module IP = Print.Int
module M = Meta

type ctx_map = pats


let rec rename_ctx_using_pats (cG : ctx) (ps : pats) =
  match cG, ps with
  | [], [] -> [], []
  | (x, t) :: cG', PVar y :: ps' ->
    let sigma, cD = rename_ctx_using_pats (ctx_subst (x, I.Var y) cG') ps' in
    (x, I.Var y) :: sigma, (y, t) :: cD
  | s :: cG', _ :: ps' ->
    let sigma, cD = rename_ctx_using_pats cG' ps' in
    sigma, s :: cD
  | _ -> raise (Error.Violation "rename_ctx_using_pats. Both arguments should have same length")


let rec subst_of_ctx_map (sigma : ctx_map) (tel : I.tel) : M.subst =
  match sigma, tel with
  | [], [] -> []
  | p :: ps, (_, n, t) :: tel' -> (n, exp_of_pat p) :: (subst_of_ctx_map ps tel')
  | _ -> raise (Error.Violation "subst_of_ctx_map got lists of different lengths")

let compose_maps (sigma : ctx_map) (cD : ctx) (delta : ctx_map) : ctx_map =
  let delta_names = List.map2 (fun (x, _) p -> x, p) cD delta in
  Debug.print(fun () -> "Composing maps\nsigma = " ^ print_pats sigma
      ^ "\ndelta = " ^ print_pats delta ^ "\ndelta_names" ^ print_psubst delta_names);
  List.map (simul_psubst delta_names) sigma

let rec matching (p : pat) (q : pat) : pats =
  match p, q with
  | PVar n, _ -> [q]
  | PPar n, PPar n' -> [PVar n']
  | PBVar i, PBVar i' when i = i' -> []
  | UInac _, _
  | IInac _, _ -> []
  | PConst (n, ps) , PConst (n', qs) when n = n' -> matchings ps qs
  | PConst (n, ps) , PConst (n', qs) -> raise(Error.Error "Pattern matching does not match.")
  | PLam (xs, p), PLam (ys, q) -> matching p q
  | PClos (n, _), PClos (n', _) -> [PVar n']
  | PNil, PNil -> []
  | _ -> raise (Error.Error ("what is love? p = " ^ print_pat p ^ " q = " ^ print_pat q))

and matchings (sigma : ctx_map) (p : pats) : pats =
  match sigma, p with
  | [], [] -> []
  | q::sigma', p :: ps -> (matching q p) @ matchings sigma' ps
  | _ -> raise (Error.Violation ("Matching lists of different size. \nsigma = " ^ print_pats sigma ^ "\np = " ^ print_pats p))

let rec flexible (p : pats)(cG : ctx) : name list =
  match p, cG with
    | [], [] -> []
    | IInac _::ps, (x, t)::cG'
    | UInac _::ps, (x, t)::cG' -> x::(flexible ps cG')
    | p::ps, (x, t)::cG' -> flexible ps cG'
    | _ -> raise (Error.Violation ("Flexible: length violation."))

let inac_ctx = List.map (fun (_, t) -> IInac t)
let inac_subst = List.map (fun (x, e) -> x, IInac e)

let split_flex_unify (sign : signature) (p1 : pats) (thetatel : I.tel) (ps : pats)
                     (cD1 : ctx) (vs : I.exp list) (ws : I.exp list) =
  let sigma, cT = rename_ctx_using_pats (ctx_of_tel thetatel) ps in
  Debug.print (fun () -> "Creating set of flexible variables\np1 = " ^ print_pats p1
    ^ "\nps = " ^ print_pats ps ^ "\ncD1 = " ^ print_ctx cD1 ^ "\ncT = " ^ print_ctx cT);
  let flex = flexible (p1 @ ps) (cD1 @ cT) in
  Debug.print (fun () -> "Flexibles variables are " ^ print_names flex);
  let vs = List.map (M.simul_subst sigma) vs in
  let ws = List.map (M.simul_subst sigma) ws in
  let cD', delta =
    Debug.print (fun () -> "Split unifies vs = " ^ IP.print_exps vs ^ ", ws = " ^ IP.print_exps ws);
    try
      Unify.unify_flex_many (sign, cD1 @ cT) flex vs ws
    with
      Unify.Unification_failure prob ->
      raise (Error.Error ("Split failed with unification problem " ^ Unify.print_unification_problem prob))
  in
  Debug.print (fun () -> "Split unification outputed : cD' = " ^ print_ctx cD');
  let cT' = simul_subst_on_ctx delta (rename_ctx_using_subst cT delta) in
  Debug.print (fun () -> "delta = " ^ IP.print_subst delta ^ ", cT = " ^ print_ctx cT ^ ", cT' = " ^ print_ctx cT');
  Debug.print (fun () -> "cD1 = " ^ print_ctx cD1);
  Debug.print (fun () -> "cT = " ^ print_ctx cT ^ "\ncT' = " ^ print_ctx cT');
  let pdelta = inac_subst delta in
  Debug.print (fun () -> "pdelta = " ^ print_psubst pdelta);
  cD', cT, delta, pdelta, cT'

let compute_split_map (ss:M.single_subst) (pss:single_psubst) (cD1:ctx) (x:name)
    (cD2:ctx) (delta : M.subst) (pdelta : psubst) (cD':ctx) : ctx * ctx_map =
  Debug.indent ();
  Debug.print (fun () -> "ss = " ^ IP.print_subst [ss]);
  Debug.print (fun () -> "pss = " ^ print_psubst [pss]);
  Debug.print (fun () -> "cD' = " ^ print_ctx cD');
  let id_cD' = psubst_of_ctx cD1 in
  let delta' = M.compose_single_with_subst ss (delta @ [x, I.Var x]) in
  Debug.print (fun () -> "delta' = " ^ IP.print_subst delta');
  let pdelta = compose_psubst pdelta id_cD' in
  Debug.print (fun () -> "pdelta = " ^ print_psubst pdelta);
  let pdelta_shift = pdelta @ [x, PVar x] in
  let pdelta' = compose_single_with_psubst pss pdelta_shift in
  Debug.print (fun () -> "pdelta' = " ^ print_psubst pdelta');
  let cD'', delta'' = cD' @ (simul_subst_on_ctx delta' cD2),
    (pats_of_psubst (shift_psubst_by_ctx pdelta' cD2)) in
  Debug.print (fun () -> "Split! \ncD2 = " ^ print_ctx cD2 ^ "\ndelta' = " ^ print_psubst pdelta'
                         ^ "\n delta'' = " ^ print_pats delta'' ^ "\n cD'' = " ^ print_ctx cD'');
  Debug.deindent ();
  cD'', delta''

let rec theta_of_lam cP xs tel =
  match xs, tel with
  | [], _ -> cP, [], tel
  | x::xs, (i,y,t)::tel' ->
     let cP', tel0, tel'' = theta_of_lam cP xs tel' in
     BSnoc(cP', x, t), (i, y, t)::tel0, tel''
  | _ -> raise (Error.Error ("Something went wrong as always"))

let rec theta_of_lam' g xs tel =
  match xs, tel with
  | [], _ -> g, [], tel
  | x::xs, (i,y,t)::tel' ->
     let g', tel0, tel'' = theta_of_lam' g xs tel' in
     I.Snoc(g', x, t), (i, y, t)::tel0, tel''
  | _ -> raise (Error.Error ("Something went wrong as always"))

let split_lam (sign : signature) (p1 : pats) (xs, p : string list * pat) (cD1 : ctx)
              (x, t : name * I.exp) (cD2 : ctx) : ctx * ctx_map =
  Debug.indent ();
  let g, tel, t = match Whnf.whnf sign t with
    | I.Box(g, I.SPi (tel, t)) -> g, tel, t
    | t -> raise (Error.Error ("Syntactic abstraction was define in a pattern against"
        ^ " type which was not syntactic function type in a box. Found " ^ IP.print_exp t))
  in
  Debug.print (fun () -> "Split SPi(" ^ IP.print_stel tel ^ ", " ^ IP.print_exp t ^ ")");
  let g', tel0, tel' = theta_of_lam' g xs tel in
  let vs = [I.Box(g, I.SPi (tel, t))] in
  let thetatel = [Syntax.Explicit, gen_floating_name (),
                  I.Box(g', if tel' = [] then t else I.SPi (tel', t))] in
  let ws = [I.Box(g, I.SPi (tel0, I.SPi(tel', t)))] in
  let cD', cT, delta, pdelta, td = split_flex_unify sign p1 thetatel [p] cD1 vs ws in
  let e = match var_list_of_ctx td with
    | [e] -> e
    | _ -> raise (Error.Violation ("Split_lam obtained more than one parameter out of td (" ^ print_ctx td ^ ")"))
  in
  let ss = x, I.Lam (xs, e) in
  let p' = match simul_psubst_on_list pdelta (pvar_list_of_ctx cT) with
    | [p'] -> p'
    | _ -> raise (Error.Violation ("Split_lam obtained more than one parameter out of substituting in cT"))
  in
  let pss = x, PLam (xs, p') in
  let res = compute_split_map ss pss cD1 x cD2 delta pdelta cD' in
  Debug.deindent (); res

let split_const (sign : signature) (p1 : pats) (c, ps : def_name * pats)
                (cD1 : ctx) (x, t : name * I.exp) (cD2 : ctx) : ctx * ctx_map =
  Debug.indent ();
  Debug.print (fun () -> "Splitting on constructor " ^ c ^ "\nSplit type " ^ IP.print_exp t) ;
  let maybe_g, n, sp =
    match Whnf.whnf sign t with
    | I.App(I.Const n, sp) -> None, n, sp
    | I.Const n -> None, n, []
    | I.Box(g, I.Const n) -> Some g, n, []
    | I.Box(g, I.App (I.Const n, sp)) -> Some g, n, sp
    | e -> raise (Error.Error ("Expected constructor application. Got " ^ IP.print_exp e))
  in
  let us, vs = split_idx_param sign n sp in
    Debug.print (fun () -> "For " ^ n ^ " the split of " ^ IP.print_exps sp
      ^ " resulted in parameters " ^ IP.print_exps us
      ^ " and indices " ^ IP.print_exps vs);
    let thetatel, (n', sp) = lookup_cons_entry c sign maybe_g in
    Debug.print (fun () -> "thetatel = " ^ IP.print_tel thetatel);
    if n = n'
    then
      let us', ws = split_idx_param sign n sp in
      let cD', cT, delta, pdelta, td = split_flex_unify sign p1 thetatel ps cD1 vs ws in
      let ss = x, I.App (I.Const c, var_list_of_ctx td) in
      let pss = x, PConst (c, simul_psubst_on_list pdelta (pvar_list_of_ctx cT)) in
      let res = compute_split_map ss pss cD1 x cD2 delta pdelta cD' in
      Debug.deindent (); res
    else
      raise (Error.Error ("Get a grip!, wrong constructor. n = \"" ^ n ^ "\"; n' = \"" ^ n' ^ "\""))

let check_ppar (sign : signature) (p1 : pats) (n : name) (cD1 : ctx)
    (x, t : name * I.exp) (cD2 : ctx) : ctx * ctx_map =
  let g, t = match Whnf.whnf sign t with
    | I.Box (I.Nil, t) -> raise (Error.Error "Matched on a parameter variable when context was expected to be empty")
    | I.Box (g, t) -> g, t
    | t -> raise (Error.Error ("Parameter variables can only be used against a boxed type. Found " ^ IP.print_exp t))
  in

  compute_split_map (x, I.Var n) (x, PPar n) cD1 x cD2 [] [] (cD1 @ [n, I.Box (g, t)])
  (* (\* let cD' = cD1 @ [n, Box (g, t)] @ (simul_subst_on_ctx [x, Var n] cD2) in *\) *)
  (* let delta =  *)

let split_clos (sign : signature) (p1 : pats) (n, s : name * pat_subst) (cD1 : ctx)
    (x, t : name * I.exp) (cD2 : ctx) : ctx * ctx_map =
  let g, t = match Whnf.whnf sign t with
    | I.Box(g, t) -> g, t
    | t -> raise (Error.Error ("Substitution on a pattern variable can "
                               ^ "only be used against a boxed type. Found "
                               ^ IP.print_exp t))
  in
  let rec get_domain g s =
    if is_ctx (sign, cD1) g then
      match g, s with
      | _, CEmpty -> I.Nil
      | _, CDot(s, y) ->
        let cP = contextify (sign, cD1 @ cD2) g in
        I.Snoc(get_domain g s, "_", lookup_bound y cP)
      | _, CShift 0 -> g
      | I.Snoc(g, _, _), CShift m -> get_domain g (CShift (m-1))
      | _, CShift m -> raise (Error.Error ("When checking pattern " ^ print_name n ^ "[" ^ print_pat_subst s
                                           ^ "], expected context " ^ IP.print_exp g ^ " to have at least "
                                           ^ string_of_int m ^ " variable" ^ if m > 1 then "s" else "" ^ " to shift over."))
    else
      raise (Error.Violation ("This should be a context " ^ IP.print_exp g))
  in
  let rec subst_of_pat_subst = function
    | CShift n -> I.Shift n
    | CEmpty -> I.EmptyS
    | CDot(s, i) -> I.Dot(subst_of_pat_subst s, I.BVar i)
  in
  match Whnf.apply_inv t s with
  | Some t -> compute_split_map (x, I.Clos(I.Var n, subst_of_pat_subst s)) (x, PClos(n, s))
                                cD1 x cD2 [] [] (cD1 @ [n, I.Box (get_domain g s, t)])
  | None -> raise (Error.Error ("Cannot check pattern matching clause " ^ print_pat (PClos (n, s))
                               ^ " because it was not possible to compute an inverse substitution for " ^ print_pat_subst s))

let split_rec (sign : signature) (ps : pats) (cD : ctx) : ctx * ctx_map =
  let rec search p1 p2 cD1 cD2 =
    match p2, cD2 with
    | [], [] -> [], []
    | PConst (c, sp) :: ps', (x, t) :: cD2 ->
       split_const sign p1 (c, sp) cD1 (x, t) cD2
    | PVar y :: ps', (x, t) :: cD2 ->
       search (p1 @ [PVar y]) ps' (cD1 @ [y, t]) (ctx_subst (x, I.Var y) cD2)
    | UInac e :: ps', (x, t) :: cD2 ->
       search (p1 @ [UInac e]) ps' (cD1 @ [x, t]) cD2
    | IInac e :: ps', (x, t) :: cD2 ->
       search (p1 @ [IInac e]) ps' (cD1 @ [x, t]) cD2
    | PPar y :: ps', (x, t) :: cD2 ->
      check_ppar sign p1 y cD1 (x, t) cD2
    | PClos (y, s) :: ps', (x, t) :: cD2 ->
      split_clos sign p1 (y, s) cD1 (x, t) cD2
    | PLam (xs, p) :: ps', (x, t) :: cD2 ->
       split_lam sign p1 (xs, p) cD1 (x, t) cD2
    | _ -> raise (Error.Error ("Search: Syntax not implemented\np2 = " ^ print_pats p2 ^ "\ncD2 = " ^ print_ctx cD2))
  in
  search [] ps [] cD

let split_set sign (x : name) (cG : ctx) : ctx_map =
  let rec f = function
    | [] -> raise (Error.Violation ("Variable " ^ print_name x ^ " appears free in context for pattern matching split."))
    | (x', t) :: cG' when x = x' -> [], t, cG'
    | (y, t) :: cG' -> let cG2, t', cG1 = f cG' in ((y, t) :: cG2), t', cG1
  in
  let cG2, t, cG1 = f cG in
  match Whnf.whnf sign t with
  | I.App(I.Const n, sp) ->
     let constrs = lookup_constructors n sign in
     let rec split_constrs constrs =
       begin match constrs with
       | [] -> []
       | c :: constrs' ->
          let thetatel, (n', sp) = lookup_cons_entry c sign None in
          let ps = (inac_ctx cG2) @ [PConst (c, inac_ctx (ctx_of_tel thetatel))] @ (inac_ctx cG1) in
          let sigma =
            try
              snd (split_rec sign ps (cG2 @ [(x, t)] @ cG1))
            with
            | Unify.Unification_failure _ -> []
          in
          sigma @ (split_constrs constrs')
       end
     in
     split_constrs constrs

  | _ -> raise (Error.Error ("Type " ^ IP.print_exp t ^ " should be a data type."))

let refine (sign : signature) (p : pats) (cD : ctx) (sigma : ctx_map) : pats * ctx * ctx_map =
  Debug.indent ();
  Debug.print (fun () -> "Refined called: p = " ^ print_pats p
                         ^ "\ncD = " ^ print_ctx cD
                         ^ "\nsigma = " ^ print_pats sigma);
  let cD', delta = split_rec sign p cD in
  Debug.print (fun () -> "Calling split_rec with cD = " ^ print_ctx cD
                         ^ "\np = " ^ print_pats p
                         ^ "\nresulting in delta = " ^ print_pats delta
                         ^ "\nand ctx cD' = " ^ print_ctx cD' ^ ".");
  let p' = matchings delta p in
  Debug.print (fun () -> "Calling matchings with delta = " ^ print_pats delta
                         ^ "\np = " ^ print_pats p ^ "\nresulting in " ^ print_pats p' ^ ".");
  let sd = compose_maps sigma cD delta in
  Debug.deindent ();
  p' , cD', sd

let check_pats (sign : signature) (p : pats) (cG : ctx) : ctx * ctx_map =
  Debug.indent ();
  let is_Pvar = function
    | PVar _ -> true
    | _ -> false
  in
  let rec unify_names p cG =
    match p, cG with
    | [], [] -> []
    | PVar x :: p', (y, t) :: cG' when x <> y -> (x, t) :: (M.compose_single_with_subst (y, I.Var x) (unify_names p' cG'))
    | _ :: p', s :: cG' -> s :: (unify_names p' cG')
    | _ -> raise (Error.Violation "Length error in unify names")
  in
  let cG' = unify_names p cG in
  let cG = cG' in
  let rec check_pats (p : pats) (sigma : ctx_map) (cD : ctx) : ctx * ctx_map =
    if List.for_all is_Pvar p then
      cD, sigma
    else
      let p', cD', sigma' = refine sign p cD sigma in
      Debug.print (fun () -> "Check pats on"
                             ^ "\np = " ^ print_pats p
                             ^ "\nsigma = " ^ print_pats sigma
                             ^ "\ncD = " ^ print_ctx cD);
      Debug.print (fun () -> "Getting from refine"
                             ^ "\np' = " ^ print_pats p'
                             ^ "\nsigma' = " ^ print_pats sigma'
                             ^ "\ncD' = " ^ print_ctx cD');

      check_pats p' sigma' cD'
  in
  let res = check_pats p (List.map (fun (x, _) -> PVar x) cG) cG in
  Debug.deindent ();
  res

let rec check_inacs (sign, cD : signature * ctx) (p : pats) (sigma : ctx_map) (cG : ctx) : I.pats =
  match p, sigma with
  | p::ps, q::qs ->
     begin match cG with
     | (x, t) :: cG' ->
        let p' = check_inac (sign, cD) p q t in
        p' :: check_inacs (sign, cD) ps qs (ctx_subst (x, M.exp_of_pat p') cG')
     | _ -> raise (Error.Error "The context ended unexpectedly.")
     end
  | [], [] -> []
  | _ -> raise (Error.Error "Size mismatch.")

and check_inacs_syn (sign, cD : signature * ctx) (cP : bctx) (p : pats) (sigma : ctx_map) (cG : ctx) : I.pats =
  match p, sigma with
  | p::ps, q::qs ->
     begin match cG with
     | (x, t) :: cG' ->
        let p' = check_inac_syn (sign, cD) cP p q t in
        p' :: check_inacs_syn (sign, cD) cP ps qs (ctx_subst (x, M.exp_of_pat p') cG')
     | _ -> raise (Error.Error "The context ended unexpectedly.")
     end
  | [], [] -> []
  | _ -> raise (Error.Error "Size mismatch.")

and check_inac (sign, cD : signature * ctx) (p : pat) (q : pat) (t : I.exp) : I.pat =
  match p, q with
  | UInac ep, UInac eq ->
     Debug.indent ();
     let ep' = check (sign, cD) ep t in
     let eq' = check (sign, cD) eq t in
     let _, sigma = try Unify.unify (sign, cD) ep' eq'
             with Unify.Unification_failure prob ->
               raise (Error.Error ("Inacessible pattern check failed with:\n" ^ Unify.print_unification_problem prob))
     in
     Debug.deindent ();
     I.Innac (M.simul_subst sigma ep')
  | UInac ep, IInac eq ->
     Debug.indent ();
     let ep' = check (sign, cD) ep t in
     let _, sigma = try Unify.unify (sign, cD) ep' eq
             with Unify.Unification_failure prob ->
               raise (Error.Error ("Inacessible pattern check failed with:\n" ^ Unify.print_unification_problem prob))
     in
     Debug.deindent ();
     I.Innac (M.simul_subst sigma ep')
  | IInac ep, _ -> raise (Error.Violation "Found internal inaccessible pattern in output. Cannot happen")
  | PVar x, PVar y when x = y -> I.PVar x
  | PPar x, PPar y when x = y -> I.PPar x
  | PConst (n, sp), PConst (n', sq) when n = n' ->
     begin match lookup_sign_entry n sign with
     | Constructor (_, tel, _) -> I.PConst (n, check_inacs (sign, cD) sp sq (ctx_of_tel tel))
     | SConstructor (_, tel, _) ->
        let g = match t with
          | I.Box(g, _) -> g
          | _ -> raise (Error.Violation ("Syntactic constructor was used to split on a non boxed type"))
        in
        I.PConst (n, check_inacs_syn (sign, cD) (contextify (sign, cD) g) sp sq (ctx_of_tel tel))
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | _ -> begin match t with
         | I.Box (g, t') -> check_inac_syn (sign, cD) (contextify (sign, cD) g) p q t'
         | _ -> raise (Error.Error ("Syntactic pattern was used against a non boxed type: " ^ Pretty.print_exp (sign, cD) BNil t))
         end


and check_inac_syn (sign, cD : signature * ctx) (cP : bctx) (p : pat) (q : pat) (t : I.exp) : I.pat =
  match p, q with
  | UInac ep, UInac eq ->
     Debug.indent ();
     let ep' = check_syn (sign, cD) cP ep t in
     let eq' = check_syn (sign, cD) cP eq t in
     let _, sigma = try Unify.unify (sign, cD) ep' eq'
             with Unify.Unification_failure prob ->
               raise (Error.Error ("Inacessible pattern check failed with:\n" ^ Unify.print_unification_problem prob))
     in
     Debug.deindent ();
     I.Innac (M.simul_subst sigma ep')
  | UInac ep, IInac eq ->
     Debug.indent ();
     let ep' = check_syn (sign, cD) cP ep t in
     let _, sigma = try Unify.unify (sign, cD) ep' eq
             with Unify.Unification_failure prob ->
               raise (Error.Error ("Inacessible pattern check failed with:\n" ^ Unify.print_unification_problem prob))
     in
     Debug.deindent ();
     I.Innac (M.simul_subst sigma ep')
  | IInac ep, _ -> raise (Error.Violation "Found internal inaccessible pattern in output. Cannot happen")
  | PVar x, PVar y when x = y -> I.PVar x
  | PPar x, PPar y when x = y -> I.PPar x
  | PConst (n, sp), PConst (n', sq) when n = n' ->
     begin match lookup_sign_entry n sign with
     | Constructor (_, tel, _) -> raise (Error.Error ("Used a data type constructor inside a syntactic pattern"))
     | SConstructor (_, tel, _) ->
        I.PConst (n, check_inacs_syn (sign, cD) cP sp sq (ctx_of_tel tel))
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | PLam (xs, p), PLam (ys, q) ->
     if List.length xs = List.length ys then
       let tel, t = begin match Whnf.whnf sign t with
                       | I.SPi (tel, t) -> tel, t
                       | t -> raise (Error.Violation ("Match - check_inac - PLam should have boxed spi type. Instead got "
                                                      ^ IP.print_exp t))
                       end
       in
       let cP', _, tel' = theta_of_lam cP xs tel in
       I.PLam (xs, check_inac_syn (sign, cD) cP' p q (if tel' = [] then t else I.SPi (tel', t)))
     else
       raise (Error.Violation "Match - check_inac - PLam binding sizes differ. Who knows why?")
  | PClos (n, s), PClos (n', s') when n = n' -> I.PClos(n, s)

  (* In the syntax cases, we might need to grow cP *)
  | p, q -> raise (Error.Error ("Pattern matching on syntax is not yet supported.\np = " ^ print_pat p ^ "\nq = " ^ print_pat q))

let check_lhs (sign : signature) (p : A.pats) (cG : ctx) : ctx * I.pats =
  let p = proc_pats p in
  let cD, sigma = check_pats sign p cG in
  Debug.print (fun () -> "Checking inacessible patterns.\ncG = " ^ print_ctx cG
    ^ "\np = " ^ print_pats p ^ "\nsigma = " ^ print_pats sigma);
  let sigma' = check_inacs (sign, cD) p sigma cG in
  cD, sigma'

let caseless (sign : signature) (cD : ctx) (x : name) (t : I.exp) : unit =
  if [] = (* snd(split sign [PVar x] ((x, t) :: cD)) *) assert false
  then ()
  else raise (Error.Error ("Pattern variable " ^ print_name x ^ " is not really impossible."))

let check_clause (sign : signature) (f : def_name) (p : A.pats) (telG : I.tel) (t : I.exp) (rhs : A.rhs) : I.pats * I.rhs =
  Debug.print (fun () -> "Checking pattern clause:\nPattern spine: " ^ AP.print_pats p
    ^ "\nRHS: " ^ AP.print_rhs rhs);
  try
    let cD, sigma = check_lhs sign p (ctx_of_tel telG) in
    Debug.print (fun () -> "LHS was checked:\n cD = " ^ print_ctx cD ^ "\n sigma = "^ IP.print_pats sigma ^ "\n telG = " ^ IP.print_tel telG);
    match rhs with
    | A.Just e ->
      let t' = M.simul_subst (M.subst_of_pats sigma telG) t in
      Debug.print (fun () -> "Checking RHS " ^ AP.print_exp e ^ " against type " ^ IP.print_exp t' ^ "\nin context " ^ print_ctx cD);
      sigma, I.Just (check (sign, cD) e t')
    | A.Impossible x -> caseless sign cD x t; sigma, I.Impossible x
  with
    Unify.Unification_failure prob ->
    raise (Error.Error ("Check clause failed for definition " ^ f
                        ^ "\nclause: " ^ AP.print_pats p
                        ^ "\nwith unification problem:\n"
                        ^ Unify.print_unification_problem prob))

let check_clauses (sign : signature) (f : def_name) (telG : I.tel) (t : I.exp) (ds : A.pat_decls) : signature * I.pat_decls =
  (* we add a non-reducing version of f to the signature *)
  let sign'=  (Program (f, telG, t, [])) :: sign in
  let ds'= List.map (fun (ps, rhs) -> check_clause sign' f ps telG t rhs) ds  in
  (Program (f, telG, t, ds')) :: sign, ds'

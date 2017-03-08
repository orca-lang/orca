open Syntax.Int
open Sign
open Check
open Name

type ctx_map = pat list

let rec subst_of_ctx_map (sigma : ctx_map) (tel : tel) : subst =
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
  | Innac e, _ ->  []
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
  Debug.indent ();
  Debug.print (fun () -> "Computing flexible variables from p = " ^ print_pats p ^ " and cG = " ^ print_ctx cG);
  let res = match p, cG with
    | [], [] -> []
    | Innac e::ps, (x, t)::cG' -> x::(flexible ps cG')
    | p::ps, (x, t)::cG' -> flexible ps cG'
    | _ -> raise (Error.Violation ("Flexible: length violation."))
  in
  Debug.print (fun () -> "Result of flexible: [" ^ (String.concat ", " (List.map print_name res)) ^ "].");
  Debug.deindent ();
  res

let innac_ctx = List.map (fun (_, t) -> Innac t)
let innac_subst = List.map (fun (x, e) -> x, Innac e)

let split_flex_unify (sign : signature) (p1 : pats) (thetatel : tel) (ps : pats) (cD1 : ctx) (vs : exp list) (ws : exp list) =
  let sigma, cT = rename_ctx_using_pats (ctx_of_tel thetatel) ps in
  Debug.print (fun () -> "Creating set of flexible variables\np1 = " ^ print_pats p1
    ^ "\nps = " ^ print_pats ps ^ "\ncD1 = " ^ print_ctx cD1 ^ "\ncT = " ^ print_ctx cT);
  let flex = flexible (p1 @ ps) (cD1 @ cT) in
  Debug.print (fun () -> "Flexibles variables are " ^ print_names flex);
  let vs = List.map (simul_subst sigma) vs in
  let ws = List.map (simul_subst sigma) ws in
  let cD', delta =
    Debug.print (fun () -> "Split unifies vs = " ^ print_exps vs ^ ", ws = " ^ print_exps ws);
    try
      Unify.unify_flex_many (sign, cD1 @ cT) flex vs ws
    with
      Unify.Unification_failure prob ->
      raise (Error.Error ("Split failed with unification problem " ^ Unify.print_unification_problem prob))
  in
  Debug.print (fun () -> "Split unification outputed : cD' = " ^ print_ctx cD');
  let cT' = simul_subst_on_ctx delta (rename_ctx_using_subst cT delta) in
  Debug.print (fun () -> "delta = " ^ print_subst delta ^ ", cT = " ^ print_ctx cT ^ ", cT' = " ^ print_ctx cT');
  Debug.print (fun () -> "cD1 = " ^ print_ctx cD1);
  Debug.print (fun () -> "cT = " ^ print_ctx cT ^ "\ncT' = " ^ print_ctx cT');
  let pdelta = innac_subst delta in
  Debug.print (fun () -> "pdelta = " ^ print_psubst pdelta);
  cD', cT, delta, pdelta, cT'

let compute_split_map (ss:single_subst) (pss:single_psubst) (cD1:ctx) (x:name)
                      (cD2:ctx) (delta : subst) (pdelta : psubst) (cD':ctx) =
  Debug.print (fun () -> "ss = " ^ print_subst [ss]);
  Debug.print (fun () -> "pss = " ^ print_psubst [pss]);
  Debug.print (fun () -> "cD' = " ^ print_ctx cD');
  let id_cD' = psubst_of_ctx cD1 in
  let delta' = compose_single_with_subst ss (delta @ [x, Var x]) in
  Debug.print (fun () -> "delta' = " ^ print_subst delta');
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

let rec theta_of_lam g xs tel =
  match xs, tel with
  | [], _ -> g, [], tel
  | x::xs, (i,y,t)::tel' ->
     let g', tel0, tel'' = theta_of_lam g xs tel' in
     Snoc(g', x, t), (i, y, t)::tel0, tel''
  | _ -> raise (Error.Error ("Somethng went wrong as always"))

let split_lam (sign : signature) (p1 : pats) (xs, p : string list * pat) (cD1 : ctx)
              (x, t : name * exp) (cD2 : ctx) : ctx * ctx_map =
  Debug.indent ();
  let g, tel, t = match Whnf.whnf sign t with
    | Box(g, SPi (tel, t)) -> g, tel, t
    | t -> raise (Error.Error ("Syntactic abstraction was define in a pattern against"
        ^ " type which was not syntactic function type in a box. Found " ^ print_exp t))
  in
  Debug.print (fun () -> "Split SPi(" ^ print_stel tel ^ ", " ^ print_exp t ^ ")");
  let g', tel0, tel' = theta_of_lam g xs tel in
  let vs = [Box(g, SPi (tel, t))] in
  let thetatel = [Syntax.Explicit, gen_floating_name (),
                  Box(g', if tel' = [] then t else SPi (tel', t))] in
  let ws = [Box(g, SPi (tel0, SPi(tel', t)))] in
  let cD', cT, delta, pdelta, td = split_flex_unify sign p1 thetatel [p] cD1 vs ws in
  let e = match var_list_of_ctx td with
    | [e] -> e
    | _ -> raise (Error.Violation ("Split_lam obtained more than one parameter out of td (" ^ print_ctx td ^ ")"))
  in
  let ss = x, Lam (xs, e) in
  let p' = match simul_psubst_on_list pdelta (pvar_list_of_ctx cT) with
    | [p'] -> p'
    | _ -> raise (Error.Violation ("Split_lam obtained more than one parameter out of substituting in cT"))
  in
  let pss = x, PLam (xs, p') in
  compute_split_map ss pss cD1 x cD2 delta pdelta cD'

let split_const (sign : signature) (p1 : pats) (c, ps : def_name * pats)
                (cD1 : ctx) (x, t : name * exp) (cD2 : ctx) : ctx * ctx_map =
  Debug.indent ();
  Debug.print (fun () -> "Split type " ^ print_exp t) ;
  let maybe_g, n, sp =
    match Whnf.whnf sign t with
    | App(Const n, sp) -> None, n, sp
    | Const n -> None, n, []
    | Box(g, Const n) -> Some g, n, []
    | Box(g, App (Const n, sp)) -> Some g, n, sp
    | e -> raise (Error.Error ("Expected constructor application. Got " ^ print_exp e))
  in
  let us, vs = split_idx_param sign n sp in
    Debug.print (fun () -> "For " ^ n ^ " the split of " ^ print_exps sp
      ^ " resulted in parameters " ^ print_exps us
      ^ " and indices " ^ print_exps vs);
    let thetatel, (n', sp) = lookup_cons_entry c sign maybe_g in
    Debug.print (fun () -> "thetatel = " ^ print_tel thetatel);
    if n = n'
    then
      let us', ws = split_idx_param sign n sp in
      let cD', cT, delta, pdelta, td = split_flex_unify sign p1 thetatel ps cD1 vs ws in
      let ss = x, App (Const c, var_list_of_ctx td) in
      let pss = x, PConst (c, simul_psubst_on_list pdelta (pvar_list_of_ctx cT)) in
      compute_split_map ss pss cD1 x cD2 delta pdelta cD'
    else
      raise (Error.Error ("Get a grip!, wrong constructor. n = \"" ^ n ^ "\"; n' = \"" ^ n' ^ "\""))

let check_ppar (sign : signature) (p1 : pats) (n : name) (cD1 : ctx)
    (x, t : name * exp) (cD2 : ctx) : ctx * ctx_map =
  let g, t = match Whnf.whnf sign t with
    | Box (Nil, t) -> raise (Error.Error "Matched on a parameter variable when context was expected to be empty")
    | Box (g, t) -> g, t
    | t -> raise (Error.Error ("Parameter variables can only be used against a boxed type. Found " ^ print_exp t))
  in
  
  compute_split_map (x, Var n) (x, PPar n) cD1 x cD2 [] [] (cD1 @ [n, Box (g, t)])
  (* (\* let cD' = cD1 @ [n, Box (g, t)] @ (simul_subst_on_ctx [x, Var n] cD2) in *\) *)
  (* let delta =  *)

let split_clos (sign : signature) (p1 : pats) (n, s : name * exp) (cD1 : ctx)
    (x, t : name * exp) (cD2 : ctx) : ctx * ctx_map =
  let g, t = match Whnf.whnf sign t with
    | Box(g, t) -> g, t
    | t -> raise (Error.Error ("Substitution on a pattern variable can "
                               ^ "only be used against a boxed type. Found "
                               ^ print_exp t))
  in
  let g' = infer_syn (sign, cD1) (contextify (sign, cD1) g) s in
  check_ctx (sign, cD1) g';
  compute_split_map (x, Var n) (x, PClos(n, s)) cD1 x cD2 [] [] (cD1 @ [n, Box (g', t)])
    
let split_rec (sign : signature) (ps : pats) (cD : ctx) : ctx * ctx_map =
  let rec search p1 p2 cD1 cD2 =
    Debug.print(fun () -> "Split search with\np1 = " ^ print_pats p1
                          ^ "\nand p2 = " ^ print_pats p2
                          ^ "\nin CD1 = " ^ print_ctx cD1
                          ^ "\nin CD2 = " ^ print_ctx cD2);
    Debug.indent();
    let cD', sigma = match p2, cD2 with
    | [], [] -> [], []
    | PConst (c, sp) :: ps', (x, t) :: cD2 ->
       split_const sign p1 (c, sp) cD1 (x, t) cD2
    | PVar y :: ps', (x, t) :: cD2 ->
       search (p1 @ [PVar y]) ps' (cD1 @ [y, t]) (ctx_subst (x, Var y) cD2)
    | Innac e :: ps', (x, t) :: cD2 ->
       search (p1 @ [Innac e]) ps' (cD1 @ [x, t]) cD2
    | PPar y :: ps', (x, t) :: cD2 ->
      check_ppar sign p1 y cD1 (x, t) cD2
    | PClos (y, s) :: ps', (x, t) :: cD2 ->
      split_clos sign p1 (y, s) cD1 (x, t) cD2
    | PLam (xs, p) :: ps', (x, t) :: cD2 ->
       split_lam sign p1 (xs, p) cD1 (x, t) cD2
    | _ -> raise (Error.Error ("Search: Syntax not implemented\np2 = " ^ print_pats p2 ^ "\ncD2 = " ^ print_ctx cD2))
    in
    Debug.print (fun () -> "Search had\ncD1 = " ^ print_ctx cD1 ^ "\ncD2 = " ^ print_ctx cD2 ^ "\nreturned cD' = " ^ print_ctx cD' ^ "\nand sigma = "^ print_pats sigma);
    cD', sigma
  in
  Debug.deindent();
  Debug.print (fun () -> "Split rec list ordering figuring out, ps = [" ^  print_pats ps ^ "], cD = " ^ print_ctx cD);
  search [] ps [] cD

let split_set sign (x : name) (cG : ctx) : ctx_map =
  let rec f = function
    | [] -> raise (Error.Violation ("Variable " ^ print_name x ^ " appears free in context for pattern matching split."))
    | (x', t) :: cG' when x = x' -> [], t, cG'
    | (y, t) :: cG' -> let cG2, t', cG1 = f cG' in ((y, t) :: cG2), t', cG1
  in
  let cG2, t, cG1 = f cG in
  match Whnf.whnf sign t with
  | App(Const n, sp) ->
     let constrs = lookup_constructors n sign in
     let rec split_constrs constrs =
       begin match constrs with
       | [] -> []
       | c :: constrs' ->
          let thetatel, (n', sp) = lookup_cons_entry c sign None in
          let ps = (innac_ctx cG2) @ [PConst (c, innac_ctx (ctx_of_tel thetatel))] @ (innac_ctx cG1) in
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

  | _ -> raise (Error.Error ("Type " ^ print_exp t ^ " should be a data type."))

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
    | PVar x :: p', (y, t) :: cG' when x <> y -> (x, t) :: (compose_single_with_subst (y, Var x) (unify_names p' cG'))
    | _ :: p', s :: cG' -> s :: (unify_names p' cG')
    | _ -> raise (Error.Violation "Length error in unify names")
  in
  let cG' = unify_names p cG in
  (* Debug.print (fun () -> "Unifying of names: cG = " ^ print_ctx cG ^ ", cG' = " *)
  (*                        ^ print_ctx cG' ^ ", using patterns p = " ^ print_pats p); *)
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

      let res = check_pats p' sigma' cD' in
      Debug.print (fun () -> "Check pats returned result ctx " ^ print_ctx (fst res) ^ "\nand pattern " ^ print_pats (snd res));
      res
  in
  let res = check_pats p (List.map (fun (x, _) -> PVar x) cG) cG in
  Debug.deindent ();
  res


let rec check_innacs (sign, cD : signature * ctx) (p : pats) (sigma : ctx_map) (cG : ctx) : unit =
  match p, sigma with
  | p::ps, q::qs ->
     begin match cG with
     | (x, t) :: cG' -> check_innac (sign, cD) p q t ; check_innacs (sign, cD) ps qs (ctx_subst (x, exp_of_pat q) cG')
     | _ -> raise (Error.Error "The context ended unexpectedly.")
     end
  | [], [] -> ()
  | _ -> raise (Error.Error "Size mismatch.")

and check_innac (sign, cD : signature * ctx) (p : pat) (q : pat) (t : exp) : unit =
  Debug.print (fun () -> "Checking inaccessible patterns.\np = "
    ^ print_pat p ^ "\nq = " ^ print_pat q);
  match p, q with
  | Innac ep, Innac eq ->
     Debug.indent ();
     check (sign, cD) ep t ;
     check (sign, cD) eq t ;
     let _ = try Unify.unify (sign, cD) ep eq
             with Unify.Unification_failure prob ->
               raise (Error.Error ("Inaccessible pattern check failed with:\n" ^ Unify.print_unification_problem prob))
     in
     Debug.deindent ();
     ()
  | PVar x, PVar y when x = y -> ()
  | PPar x, PPar y when x = y -> ()
  | PConst (n, sp), PConst (n', sq) when n = n' ->
     begin match lookup_sign_entry n sign with
     | Constructor (_, tel, _) -> check_innacs (sign, cD) sp sq (ctx_of_tel tel)
     | SConstructor (_, tel, _) ->
        let box_ctx g = List.map (fun (x, t) -> x, Box (g, t)) in
        let g = match t with
          | Box(g, _) -> g
          | _ -> raise (Error.Violation ("Syntactic constructor was used to split on a non boxed type"))
        in
        check_innacs (sign, cD) sp sq (box_ctx g (ctx_of_tel tel))
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | PLam (xs, p), PLam (ys, q) ->
     if List.length xs = List.length ys then
       let g, tel, t = begin match Whnf.whnf sign t with
                       | Box (g, SPi (tel, t)) -> g, tel, t
                       | t -> raise (Error.Violation ("Match - Check_innac - PLam should have boxed spi type. Instead got "
                                                      ^ print_exp t))
                       end
       in
       let g', _, tel' = theta_of_lam g xs tel in
       check_innac (sign, cD) p q (Box(g', if tel' = [] then t else SPi (tel', t)))
     else
       raise (Error.Violation "Match - Check_innac - PLam binding sizes differ. Who knows why?")
  | PClos (n, _), PClos (n', _) when n = n' -> ()

  (* In the syntax cases, we might need to grow cP *)
  | p, q -> raise (Error.Error ("Pattern matching on syntax is not yet supported.\np = " ^ print_pat p ^ "\nq = " ^ print_pat q))

let check_lhs (sign : signature) (p : pats) (cG : ctx) : ctx * ctx_map =
  let cD, sigma = check_pats sign p cG in
  Debug.print (fun () -> "Checking LHS returned\ncD = " ^ print_ctx cD ^ "\nsigma = " ^ print_pats sigma);
  Debug.print (fun () -> "Checking inaccessible with \ncG = " ^ print_ctx cG ^ "\np = " ^ print_pats p);
  check_innacs (sign, cD) p sigma cG ;
  cD, sigma

let caseless (sign : signature) (cD : ctx) (x : name) (t : exp) : unit =
  if [] = (* snd(split sign [PVar x] ((x, t) :: cD)) *) assert false
  then ()
  else raise (Error.Error ("Pattern variable " ^ print_name x ^ " is not really impossible."))

let check_clause (sign : signature) (f : def_name) (p : pats) (telG : tel) (t : exp) (rhs : rhs) : unit =
  Debug.print (fun () -> "Checking pattern clause:\nPattern spine: " ^ print_pats p
    ^ "\nRHS: " ^ print_rhs rhs);
  try
    let cD, sigma = check_lhs sign p (ctx_of_tel telG) in
    Debug.print (fun () -> "LHS was checked:\n cD = " ^ print_ctx cD ^ "\n sigma = "^ print_pats sigma ^ "\n telG = " ^ print_tel telG);
    match rhs with
    | Just e -> check (sign, cD) e (simul_subst (subst_of_ctx_map sigma telG) t)
    | Impossible x -> caseless sign cD x t
  with
    Unify.Unification_failure prob ->
    raise (Error.Error ("Check clause failed for definition " ^ f
                        ^ "\nclause: " ^ print_pats p
                        ^ "\nwith unification problem:\n"
                        ^ Unify.print_unification_problem prob))

let check_clauses (sign : signature) (f : def_name) (telG : tel) (t : exp) (ds : pat_decls) : signature =
  (* we add a non-reducing version of f to the signature *)
  let sign'=  (Program (f, telG, t, [])) :: sign in
  List.iter (fun (ps, rhs) -> check_clause sign' f ps telG t rhs) ds ;
  (Program (f, telG, t, ds)) :: sign

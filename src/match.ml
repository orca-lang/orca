open Syntax.Int
open Sign
open Check
open Name

type ctx_map = pat list

let compose_maps (sigma : ctx_map) (cD : ctx) (delta : ctx_map) : ctx_map =
  List.map (fun (_, e) -> pat_of_exp e) (compose_subst (List.map2 (fun (x, _) p -> x, exp_of_pat p) cD delta)
                                     (List.map (fun x -> gen_floating_name (), exp_of_pat x) sigma))

let rec matching (p : pat) (q : pat) : pats =
  match p, q with
  | PVar n, _ -> [q]
  | Innac e, _ ->  []
  | PConst (n, ps) , PConst (n', qs) when n = n' -> matchings ps qs
  | PConst (n, ps) , PConst (n', qs) -> raise(Error.Error "Pattern matching does not match.")
  | _ -> raise (Error.Error ("what is love? p = " ^ print_pat p ^ " q = " ^ print_pat q)) (* assert false (\* TODO cases for syntax *\) *)


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

exception Unification_failure

let split (sign : signature) (p1 : pats) (c, ps : def_name * pats) (cD2 : ctx) (x, t : name * exp) (cD1 : ctx) : ctx * ctx_map =
  let n, sp =
    match Whnf.whnf sign t with
    | App(Const n, sp) -> n, sp
    | Const n -> n, []
    | e -> raise (Error.Error ("Expected constructor application. Got " ^ print_exp e))
  in
  let us, vs = split_idx_param sign n sp in
  let thetatel, (n', sp) = lookup_cons_entry c sign in
  if n = n'
  then
    let us', ws = split_idx_param sign n sp in
    let cT = ctx_of_tel thetatel in
    let flex = flexible (ps @ p1) (cT @ cD1) in
    let cD', delta =
      try
        Unify.unify_flex_many (sign, cT @ cD1) flex vs ws
         with
         | Error.Error _ -> raise Unification_failure
    in
    let cT' = compose_subst delta cT in
    let ss = x, App (Const c, exp_list_of_ctx cT') in
    let delta_shift = shift_subst_by_ctx delta [ss] in
    let delta' = compose_single_with_subst ss delta_shift in
    let cD'', delta'' = (subst_list_on_ctx delta' cD2) @ cD', pats_of_exps (exp_list_of_ctx (shift_subst_by_ctx delta' cD2)) in
    Debug.print (fun () -> "Split! \ncD2 = " ^ print_ctx cD2 ^ "\ndelta' = " ^ print_ctx delta'
                           ^ "\n delta'' = " ^ print_pats delta'' ^ "\n cD'' = " ^ print_ctx cD'');
    cD'', delta''
  else
    raise (Error.Error ("Get a grip!, wrong constructor. n = \"" ^ n ^ "\"; n' = \"" ^ n' ^ "\""))

let split_rec (sign : signature) (ps : pats) (cD : ctx) : ctx * ctx_map =
  let rec search p1 p2 cD1 cD2 =
  match p2, cD2 with
  | [], [] -> [], []
  | PConst (c, sp) :: ps', (x, t) :: cD2 ->
     split sign p1 (c, sp) cD2 (x, t) cD1
  | PVar y :: ps', (x, t) :: cD2 ->
     search (p1 @ [PVar y]) ps' (cD1 @ [x, t]) cD2
  | _ -> raise (Error.Error ("Syntax not implemented\np2 = " ^ print_pats p2 ^ "\ncD2 = " ^ print_ctx cD2))
  in
  Debug.print (fun () -> "Split rec list ordering figuring out, ps = [" ^  print_pats ps ^ "], cD = " ^ print_ctx cD);
  search [] ps [] cD

let innac_ctx = List.map (fun (_, t) -> Innac t)

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
          let thetatel, (n', sp) = lookup_cons_entry c sign in
          let ps = (innac_ctx cG2) @ [PConst (c, innac_ctx (ctx_of_tel thetatel))] @ (innac_ctx cG1) in
          let sigma =
            try
              snd (split_rec sign ps (cG2 @ [(x, t)] @ cG1))
            with
            | Unification_failure -> []
          in
          sigma @ (split_constrs constrs')
       end
     in
     split_constrs constrs

  | _ -> raise (Error.Error ("Type " ^ print_exp t ^ " should be a data type."))

let refine (sign : signature) (p : pats) (cD : ctx) (sigma : ctx_map) : pats * ctx * ctx_map =
  let cD', delta = split_rec sign p cD in
    Debug.print (fun () -> "Calling split_rec with cD = [" ^ print_ctx cD
                           ^ "], p = [" ^ print_pats p ^ "], resulting in delta = ["
                           ^ print_pats delta ^ "] and ctx cD' = [" ^ print_ctx cD' ^ "]");
  let p' = matchings delta p in
  Debug.print (fun () -> "Calling matchings with delta = [" ^ print_pats delta
                         ^ "], p = [" ^ print_pats p ^ "], resulting in [" ^ print_pats p' ^ "].");
  let sd = compose_maps sigma cD delta in
  p' , cD', sd

let check_pats (sign : signature) (p : pats) (cG : ctx) : ctx * ctx_map =
  let is_Pvar = function
    | PVar _ -> true
    | _ -> false
  in
  let rec unify_names p cG =
    match p, cG with
    | [], [] -> []
    | PVar x :: p', (y, t) :: cG' when x <> y -> (x, t) :: (compose_single_with_subst (x, t) (unify_names p' cG'))
    | _ :: p', s :: cG' -> s :: (unify_names p' cG')
    | _ -> raise (Error.Violation "Length error in unify names")
  in
  let cG = unify_names p cG in
  let rec check_pats (p : pats) (sigma : ctx_map) (cD : ctx) : ctx * ctx_map =
    if List.for_all is_Pvar p then
      cD, sigma
    else
      let p', cD', sigma' = refine sign p cD sigma in
      Debug.indent ();
      Debug.print (fun () -> "Check pats on");
      Debug.indent ();
      Debug.print (fun () -> "p = " ^ print_pats p);
      Debug.print (fun () -> "sigma = " ^ print_pats sigma);
      Debug.print (fun () -> "cD = " ^ print_ctx cD);
      Debug.deindent ();
      Debug.print (fun () -> "Getting from refine");
      Debug.indent ();
      Debug.print (fun () -> "p' = " ^ print_pats p');
      Debug.print (fun () -> "sigma' = " ^ print_pats sigma');
      Debug.print (fun () -> "cD' = " ^ print_ctx cD');
      Debug.deindent ();Debug.deindent ();

      let res = check_pats p' sigma' cD' in
      Debug.deindent ();
      res
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
     let _ = Unify.unify (sign, cD) ep eq in
     ()
  | PVar x, PVar y (* when x = y *) -> () (* Norell requires both variables *)
  | PConst (n, sp), PConst (n', sq) when n = n' ->
     begin match lookup_sign_entry n sign with
     | Constructor (_, tel, _) -> check_innacs (sign, cD) sp sq (ctx_of_tel tel)
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | p, q -> raise (Error.Error ("Pattern matching on syntax is not yet supported.\np = " ^ print_pat p ^ "\nq = " ^ print_pat q))

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

open Meta
open Sign
open Name

module A = Syntax.Apx
module AP = Print.Apx

module I = Syntax.Int
module IP = Print.Int

let is_syntax = function
  | A.Lam _
  | A.AppL _
  | A.App _
  | A.Const _
  | A.Var _
  | A.BVar _
  | A.Clos _
  | A.EmptyS
  | A.Shift _
  | A.Dot _
  | A.Snoc _
  | A.Nil -> true
  | _ -> false

let lookup x cG =
  begin
    try List.assoc x cG
    with Not_found ->
      raise (Error.Violation
               ("Unbound var after preprocessing, this cannot happen. (Var: " ^ print_name x ^ ")"))
  end

let is_ctx (sign, cG) = function
  | I.Nil
  | I.Snoc _ -> true
  | I.Var g when lookup g cG = I.Ctx -> true
  | _ -> false

let rec contextify (sign, cG) (g : I.exp) =
  match Whnf.whnf sign g with
  | I.Nil -> BNil
  | I.Var x ->
    begin match lookup x cG with
    | I.Ctx -> CtxVar x
    | _ -> raise (Error.Violation ("Tried to contextify non context variable " ^ print_name x))
    end
  | I.Snoc (g', x, e) ->
    let cP = contextify (sign, cG) g' in
    (* is_syn_type (sign, cG) cP e; *)
    BSnoc (cP, x, e)
  | _ -> raise (Error.Error ("Expected context, obtained " ^ IP.print_exp g))

let rec decontextify cP =
  match cP with
  | BNil -> I.Nil
  | CtxVar x -> I.Var x
  | BSnoc (cP', x, e) -> I.Snoc (decontextify cP', x, e)

let unify_ctx (sign, cG) e g cP =
  let g' = decontextify cP in
  Debug.print(fun () -> "Unifying contexts.\ng  = " ^ IP.print_exp g ^ "\ng' = " ^ IP.print_exp g' ^ "\n with ctx " ^ print_ctx cG);
  let cD, sigma =
    try
      Unify.unify (sign, cG) g g'
    with
      Unify.Unification_failure problem ->
        Debug.print (fun () -> Unify.print_unification_problem problem);
        raise (Error.Error (IP.print_exp e ^ " is defined in bound context " ^ IP.print_exp g
                            ^ " but it was expected to be in bound context " ^ IP.print_exp g'))
  in
  cD, sigma


let check_box (sign, cG) cP e = function
  | I.Box (g, t) ->
    let cD, sigma = unify_ctx (sign, cG) e g cP in
    simul_subst sigma e, simul_subst sigma t
  | t -> e, t

(* infers the type and returns the internal term and its type *)
let rec infer (sign, cG : signature * ctx) (e : A.exp) : I.exp * I.exp =
  Debug.print (fun () -> "Infer called with: " ^ AP.print_exp e ^ " in context: " ^ print_ctx cG);
  Debug.indent() ;
  let res_e, res_t  =
    match e with
    | A.Annot (e, t) ->
       let t', _ = infer_type (sign, cG) t in
       check (sign, cG) e t', t'
    | A.Const n ->
       I.Const n, lookup_sign sign n
    | A.Var n -> I.Var n, lookup n cG
    | A.App (h, sp) ->
      begin match infer (sign, cG) h with
       | h', I.Pi (tel, t) ->
          let sp', t' = check_spine (sign, cG) sp tel t in
          I.App (h', sp'), t'


       | _, (I.SPi _ as t) ->
         raise (Error.Error ("The left hand side (" ^ AP.print_exp h ^ ") was expected to be of extensional "
                             ^ "function type while it was found to be of intensional function type " ^ IP.print_exp t))

       | _, t -> raise (Error.Error ("The left hand side (" ^ AP.print_exp h ^ ") of the application was of type "
                                  ^ IP.print_exp t ^ " which is not of function type"))
       end

    | A.Set n -> I.Set n, I.Set (n + 1)
    | A.Pi (tel, t) ->
       check_pi (sign, cG) tel t

    | A.Ctx -> I.Ctx, I.Set 0
    | A.Box (g, e) ->
      let g' = check_ctx (sign, cG) g in
      let cP = contextify (sign, cG) g' in
      let e' = check_syn_type (sign, cG) cP e in
      I.Box(g', e'), I.Set 0

    | _ ->
      Debug.print (fun() -> "Was asked to infer the type of " ^ AP.print_exp e
        ^ " but the type is not inferrable") ;
      raise (Error.Error ("Cannot infer the type of "))
  in
  Debug.deindent ();
  Debug.print(fun() -> "Result of infer for " ^ AP.print_exp e ^ " was " ^ IP.print_exp res_t) ;
  res_e, res_t

and infer_type (sign, cG : signature * ctx) (s : A.exp) : I.exp * I.universe =
  match infer (sign, cG) s with
  | t, I.Set n -> t, n
  | t, e ->
     Debug.print (fun () -> "Assert universe failed for " ^ IP.print_exp e ^ ".") ;
     raise (Error.Error "Not a universe.")

and check (sign , cG : signature * ctx) (e : A.exp) (t : I.exp) : I.exp =
  Debug.print (fun () ->
      "Checking " ^ AP.print_exp e ^ "\nagainst "
      ^ Pretty.print_exp (sign, cG) BNil t ^ "\nin context: " ^ print_ctx cG);
  Debug.indent();
  let res_e = match e, Whnf.whnf sign t with
    (* checkable terms *)
    | A.Hole n, _ -> I.Hole n  (* holes are always of the right type *)
    | A.Fn (fs, e), I.Pi(tel, t) ->
       let sigma = List.map2 (fun f (_, n, _) -> n, I.Var f) fs tel in
       let t' = simul_subst sigma t in
       let cG' = simul_subst_on_ctx sigma cG in
       let cGext = List.map2 (fun f (_, _, s) -> f, s) fs (simul_subst_on_tel sigma tel) in
       Debug.indent();
       Debug.print (fun () -> "Checking function: " ^ AP.print_exp (A.Fn (fs, e)) ^ "\nin context " ^ print_ctx cG ^ ".");
       Debug.print (fun () -> "Resulted in ctx " ^ print_ctx cG'
                              ^ "\nwith extension " ^ print_ctx cGext
                              ^ "\nwith renaming " ^ IP.print_subst sigma ^ ".");
       let e' = check (sign, cGext @ cG') e t' in
       Debug.deindent() ;
       I.Fn (fs, e')

    | _, I.Box (g, alpha) when is_syntax e ->
       let cP = contextify (sign, cG) g in
       check_syn (sign, cG) cP e alpha

    | _, I.Ctx when is_syntax e -> check_ctx (sign, cG) e

    | _ ->
       let e, t' =
         try infer (sign, cG) e
         with Error.Error msg ->
           Debug.print_string msg;
           raise (Error.Error ("Cannot check expression " ^ AP.print_exp e ^ "\n" ^ msg))
       in
       try
         let _, sigma =
           Unify.unify (sign, cG) t t' in
         Debug.print (fun () -> "Unification for " ^ IP.print_exp t ^ " with " ^
                                  IP.print_exp t' ^ " succeeded with substitution "
                                  ^ Unify.print_subst sigma ^ ".");
         simul_subst sigma e
       with
       | Unify.Unification_failure prob ->
          let string_e = IP.print_exp e in
          let string_t = IP.print_exp t in
          let string_t' = IP.print_exp t' in
          let message = "Expression: " ^ string_e
                        ^ "\nwas inferred type: " ^ string_t'
                        ^ "\nwhich is not equal to: " ^ string_t ^ " that was checked against."
                        ^ "\nUnification failed with " ^ Unify.print_unification_problem prob
          in
          Debug.print_string message;
          raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))
  in
  Debug.deindent();
  Debug.print (fun() -> "Finished check for " ^ AP.print_exp e) ;
  res_e

and check_spine (sign, cG) sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
     let e' = check (sign, cG) e s in
     let tel', t' = subst_pi (x, e') tel t in
     let sp', t'' = check_spine (sign, cG) sp' tel' t' in
     e'::sp', t''
  | [], [] -> [], t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      | I.Pi (tel', t') -> check_spine (sign, cG) sp tel' t'
      | I.Box (g, I.SPi (tel', t')) ->
        let cP = contextify (sign, cG) g in
        check_spi_spine (sign, cG) cP sp tel' t'
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ IP.print_exp t))
    end
  | [], _ -> [], I.Pi (tel, t)

and check_pi (sign, cG) tel t =
  match tel with
  | [] -> infer (sign, cG) t
  | (i, x, s)::tel' ->
     let s', us = infer_type (sign, cG) s in
     let t', ut = check_pi (sign, (x, s')::cG) tel' t in
     let t'' = match t' with
       | I.Pi(tel, t) -> I.Pi((i, x, s')::tel, t)
       | t -> I.Pi([i, x, s'], t)
     in
     begin match ut with
     | I.Set 0 -> t'', I.Set 0 (* Set 0 is impredicative *)
     | I.Set n -> t'', I.Set (max us n)
     | _ -> raise (Error.Error ("Expression " ^ AP.print_exp (A.Pi(tel,t)) ^ " cannot be checked to be a type."))
     end

and check_syn_type (sign, cG) cP (e : A.exp) : I.exp =
  Debug.print (fun () -> "Checking syntactic type " ^ AP.print_exp e ^ "\nin context " ^ print_ctx cG);
  Debug.indent ();
  let res =
    match e with
    | A.Star -> I.Star
    | A.SPi (tel, e') ->
      let rec check_stel_type cP = function
        | [] -> [], cP
        | (i, x, s) :: tel ->
           let s' = check_syn_type (sign, cG) cP s in
           let tel', cP' = check_stel_type (BSnoc (cP, x, s')) tel in
          (i, x, s') :: tel', cP'
      in
      let tel', cP' = check_stel_type cP tel in
      I.SPi (tel', check_syn_type (sign, cG) cP' e')
    | A.Pi (tel, e') ->
      let rec check_tel_type cG = function
        | [] -> []
        | (i, x, s) :: tel ->
          let s' = check_syn_type (sign, cG) cP s in
          (i, x, s') :: (check_tel_type ((x, s') :: cG) tel)
      in
      let tel' = check_tel_type cG tel in
      let e'' = check_syn_type (sign, cG) cP e' in
      I.Pi(tel', e'')
    | A.Const n -> if lookup_syn_def n sign = [] then I.Const n
      else raise (Error.Error ("Type " ^ n ^ " is not fully applied."))
    | A.App (A.Const n, es) ->
      let tel = lookup_syn_def n sign in
      begin try
          I.App (I.Const n, List.map2 (fun e (_, x, t) -> check_syn (sign, cG) cP e t) es tel)
        with Invalid_argument _ -> raise (Error.Error ("Type " ^ n ^ " is not fully applied."))
      end
    | _ -> raise (Error.Error (AP.print_exp e ^ " is not a syntactic type."))
  in Debug.deindent (); res

and check_ctx (sign, cG) g =
  match g with
  | A.Snoc (g, x, e) ->
    let g' = check_ctx (sign, cG) g in
    let cP' = contextify (sign, cG) g' in
    I.Snoc (g', x, check_syn_type (sign, cG) cP' e)
  | A.Nil -> I.Nil
  | A.Var x ->
    begin match lookup x cG with
    | I.Ctx -> I.Var x
    | _ -> raise (Error.Error ("Variable " ^ print_name x ^ " was expected to be a context variable."))
    end
  | _ -> raise (Error.Error ("Expression " ^ AP.print_exp g ^ " was expected to be a context."))


and check_syn (sign, cG) cP (e : A.exp) (t : I.exp) =
  Debug.print (fun () -> "Checking syntactic expression " ^ AP.print_exp e
    ^ "\nagainst type " ^ Pretty.print_exp (sign, cG) cP t ^ "\nin bound context "
    ^ print_bctx cP ^ "\nand context " ^ print_ctx cG);
  Debug.indent ();
  let res =
    match e, Whnf.whnf sign t with
    | A.Lam (f, e), I.SPi (tel, t) ->
       let cP', tel' = bctx_of_lam_stel f tel cP in
       (* let cP'' = append_bctx cP' cP in *)
      begin match tel' with
      | [] -> I.Lam (f, check_syn (sign, cG) cP' e t)
      | _ -> I.Lam (f, check_syn (sign, cG) cP' e (I.SPi (tel', t)))
      end
    | _, I.Ctx -> check_ctx (sign, cG) e
    | A.EmptyS, I.Nil -> I.EmptyS
    | A.Shift n, g when is_ctx (sign, cG) g ->
      let g' = decontextify (drop_suffix cP n) in
      let _ = try Unify.unify (sign, cG) g g'
        with Unify.Unification_failure prob ->
          raise (Error.Error ("Expected context: " ^ IP.print_exp g ^ " shifted by " ^ string_of_int n
                              ^ " position" ^ (if n > 1 then "s" else "")
                              ^".\nFound context: " ^ IP.print_exp g' ^ "\nUnification failed with : "
                              ^ Unify.print_unification_problem prob))
      in I.Shift n
    | A.Dot (s, e), I.Snoc (g, _, t) ->
      let s' = check_syn (sign, cG) cP s g in
      I.Dot (s', check_syn (sign, cG) cP e (I.Clos(t, s')))
    | e, t when is_syntax e ->
      Debug.print(fun ()-> "Expression " ^ AP.print_exp e ^ " is syntactic and thus being inferred");
      let e', t' = match infer_syn (sign, cG) cP e with
        | e, I.Box (g, t) ->
          let cD, sigma = unify_ctx (sign, cG) t g cP in
          simul_subst sigma e, simul_subst sigma t
        | e, t -> e, t
      in
      let _, sigma = try
          Unify.unify (sign, cG) t t'
      with
        Unify.Unification_failure prob ->
          raise (Error.Error ("Checking syntactic term " ^ AP.print_exp e ^ " against type " ^ IP.print_exp t
                              ^ "\nIn context " ^ print_bctx cP
                            ^ "\nFailed with unification problem:\n" ^ Unify.print_unification_problem prob))
      in
      simul_subst sigma e'
    | e, t ->
      Debug.print(fun ()-> "Expression " ^ AP.print_exp e ^ " is not syntactic and thus back to check");
      check (sign, cG) e (I.Box (decontextify cP, t))
  in Debug.deindent (); res

and infer_syn (sign, cG) cP (e : A.exp) =
  Debug.print (fun () -> "Inferring type of syntactic expression " ^ AP.print_exp e
    ^ "\nin bound context " ^ print_bctx cP ^ "\nand context " ^ print_ctx cG);
  Debug.indent ();
  let res =
    match e with
    | A.SPi (tel, t) ->
       let tel', t' = check_spi (sign, cG) cP tel t in
       I.SPi (tel', t'), I.Star
    | A.App (e, es) ->
      begin match infer_syn (sign, cG) cP e with
      | e', I.Pi (tel, t) ->
         let es', t' = check_syn_spine (sign, cG) cP es tel t in
         I.App (e', es'), t'
      | _ -> raise (Error.Error "Term in function position is not of function type")
      end

    | A.AppL (e, es) ->
       let e', t' = infer_syn (sign, cG) cP e in
      begin match Whnf.whnf sign t' with
      | I.SPi (tel, t) ->
         let es', t' = check_spi_spine (sign, cG) cP es tel t in
         I.AppL(e', es'), t'
      | t -> raise (Error.Error ("Term in function position is not of function type. Instead " ^ IP.print_exp t))
      end
    | A.Var x ->
      Debug.print (fun () -> "Variable " ^ print_name x ^ " is being looked up in context " ^ print_ctx cG);
      check_box (sign, cG) cP (I.Var x) (lookup x cG)
    | A.Const n -> check_box (sign, cG) cP (I.Const n) (lookup_sign sign n)
    | A.BVar i ->
       let t = lookup_bound i cP in
       Debug.print (fun () -> "Looking bound variable " ^ string_of_int i ^ " resulted in type " ^ IP.print_exp t
                              ^ "\n Context is " ^ print_bctx cP);
       I.BVar i, t
    | A.Clos (e, s) ->
      begin
        let e', t = try infer (sign, cG) e
          with Error.Error msg ->
            Debug.print (fun () -> "Inferring " ^ AP.print_exp e ^ " returned message:\n" ^ msg);
            raise (Error.Error ("Unable to infer the left hand side of the closure " ^ AP.print_exp (A.Clos (e, s))
                                ^ "\nbecause " ^ msg ^"."))
        in
        match t with
        | I.Box(g, t) ->
          let s' = check_syn (sign, cG) cP s g in
          I.Clos (e', s'), I.Clos(t, s')
        | _ -> raise (Error.Error ("Expected " ^ AP.print_exp e ^ " to be of boxed type. Instead inferred type " ^ IP.print_exp t))
      end
    | _ -> raise (Error.Error ("Cannot infer syntactic expression " ^ AP.print_exp e))
  in Debug.deindent (); res

and check_syn_spine (sign, cG) cP sp tel t =
  Debug.print (fun () -> "Checking syn spine:\nsp = " ^ AP.print_exps sp ^ "\ntel = " ^ IP.print_tel tel);
  Debug.indent ();
  let res = match sp, tel with
    | e::sp', (_, x, s)::tel ->
      let e' = match Whnf.whnf sign s with
        | I.Box(g, s) ->
           (* we forget about cP and go on with g... MMMM *)
           check_syn (sign, cG) (contextify (sign, cG) g) e s
        | s -> check_syn (sign, cG) cP e s
      in
      Debug.print (fun () -> "Checking syn spine:\ne = " ^ AP.print_exp e ^ "\ns = " ^ IP.print_exp s);
      let tel', t' = subst_pi (x, e') tel t in
      let sp'', t'' = check_syn_spine (sign, cG) cP sp' tel' t' in
      e'::sp'', t''
  | [], [] -> [], t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      | I.Pi (tel', t') -> check_syn_spine (sign, cG) cP sp tel' t'
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ IP.print_exp t))
    end
  | [], _ -> [], I.Pi (tel, t)
  in
  Debug.deindent ();
  res

and check_spi_spine (sign, cG) cP sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
    let e' = check_syn (sign, cG) cP e s in
    let wrap t = I.Clos (t, (I.Dot (I.Shift 1, e'))) in
    let tel' = List.map (fun (i, n, e) -> i, n, wrap e) tel in
    let sp'', t' = check_spi_spine (sign, cG) cP sp' tel' (wrap t) in
    e'::sp'', t'
  | [], [] -> [], t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      (* Not sure if Pi's are allowed inside boxes *)
      (* | Pi (tel', t') -> check_spine (sign, cG) sp tel' t' *)
      | I.SPi (tel', t') -> check_spi_spine (sign, cG) cP sp tel' t
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ IP.print_exp t))
    end
  | [], _ -> [], I.SPi (tel, t)

and check_spi (sign, cG) cP (tel : A.stel) t =
  match tel with
  | [] -> [], check_syn_type (sign, cG) cP t
  | (i, x, s)::tel' ->
     let s' = check_syn_type (sign, cG) cP s in
     let tel'', t' = check_spi (sign, cG) (BSnoc (cP, x, s')) tel' t in
     ((i, x, s')::tel''), t'

let rec check_tel (sign, cG) u tel =
  match tel with
  | [] -> [], u
  | (i, x, s) :: tel' ->
     let s', us = infer_type (sign, cG) s in
     let tel', u' =
       if u = 0 then
         check_tel (sign, (x, s') :: cG) u tel'
     else
       let u' = max us u in
       Debug.print (fun () -> "Checking telescope at variable " ^ print_name x
                           ^ " which has universe " ^ IP.print_universe us
                           ^ " upgrading telescope's universe from "
                           ^ IP.print_universe u ^ " to " ^ IP.print_universe u');
       check_tel (sign, (x, s') :: cG) u' tel'
     in
     (i, x, s')::tel', u'


let rec check_syn_tel (sign, cG) tel =
  match tel with
  | [] -> []
  | (i, x, s) :: tel' ->
    let s' = check_syn_type (sign, cG) BNil s in
    (i, x, s') :: (check_syn_tel (sign, (x, s') :: cG) tel')

let rec check_stel (sign, cG) cP tel =
  match tel with
  | [] -> []
  | (i, x, s) :: tel' ->
    let s' = check_syn_type (sign, cG) cP s in
    (i, x, s'):: (check_stel (sign, cG) (BSnoc (cP, x, s')) tel')
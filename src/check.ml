open Syntax.Int
open Sign
open Name

let is_syntax = function
  | Lam _
  | AppL _
  | Const _
  | Var _
  | BVar _
  | Clos _
  | EmptyS
  | Shift _
  | ShiftS _
  | Comp _
  | Dot _
  | Snoc _
  | Nil
  | Under -> true
  | _ -> false

let lookup x cG =
  begin
    try List.assoc x cG
    with Not_found ->
      raise (Error.Violation
               ("Unbound var after preprocessing, this cannot happen. (Var: " ^ print_name x ^ ")"))
  end

let rec contextify (sign, cG) (g : exp) =
  match Whnf.whnf sign g with
  | Nil -> BNil
  | Var x ->
    begin match lookup x cG with
    | Ctx -> CtxVar x
    | _ -> raise (Error.Violation ("Tried to contextify non context variable " ^ print_name x))
    end
  | Snoc (g', x, e) ->
    let cP = contextify (sign, cG) g' in
    (* is_syn_type (sign, cG) cP e; *)
    BSnoc (cP, x, e)
  | _ -> raise (Error.Error ("Expected context, obtained " ^ print_exp g))

let rec decontextify cP =
  match cP with
  | BNil -> Nil
  | CtxVar x -> Var x
  | BSnoc (cP', x, e) -> Snoc (decontextify cP', x, e)

let unify_ctx (sign, cG) g cP =
  let g' = decontextify cP in
  Debug.print(fun () -> "Unifying contexts.\ng  = " ^ print_exp g ^ "\ng' = " ^ print_exp g' ^ "\n with ctx " ^ print_ctx cG);
  let cD, sigma = try
      Unify.unify (sign, cG) g g'
    with
      Unify.Unification_failure problem ->
      raise (Error.Error ("Unification of context:\ng  = " ^ print_exp g
                          ^ "\nand\ng' = " ^ print_exp g'
                          ^ "\nfailed with the following problem:\n" ^ Unify.print_unification_problem problem))
  in
  let cP' = contextify (sign, cG) (simul_subst sigma g) in
  cD, sigma, cP'

let check_box (sign, cG) cP = function
  | Box (g, t) ->
    let cD, sigma, cP' = unify_ctx (sign, cG) g cP in
    simul_subst sigma t
    (* else raise (Error.Error "Wrong contexts. Tip: use a substitution?") *)
  | t -> t
(* raise (Error.Error "Not a box. Don't think outside of the box.") *)

let rec infer (sign, cG : signature * ctx) (e : exp) : exp =
  Debug.print (fun () -> "Infer called with: " ^ print_exp e ^ " in context: " ^ print_ctx cG);
  Debug.indent() ;
  let res =
    match e with
    | Annot (e, t) ->
       check (sign, cG) e t ; t
    | Const n ->
       lookup_sign sign n
    | Var n -> lookup n cG
    | App (h, sp) ->
      begin match infer (sign, cG) h with
       | Pi (tel, t) ->
         check_spine (sign, cG) sp tel t
       (* | SPi (tel, t) -> *)
       (*   check_syn_spine (sign, cG) cP sp tel t *)
       (* | Box (g, SPi (tel, t)) -> *)
       (*   let cD, sigma, cP' = unify_ctx (sign, cG) g cP in *)
       (*   Box (g, check_syn_spine (sign, cD) cP' sp (simul_subst_on_stel sigma tel) (simul_subst sigma t)) *)
       | t -> raise (Error.Error ("The left hand side (" ^ print_exp h ^ ") of the application was of type "
                                  ^ print_exp t ^ " which is not of function type"))
       end

    | Set n -> Set (n + 1)
    | Pi (tel, t) ->
       check_pi (sign, cG) tel t

    | Box (g, e) ->
      check (sign, cG) g Ctx;
      let cP = contextify (sign, cG) g in
      check_syn_type (sign, cG) cP e;
      Set 0

    | _ ->
      Debug.print (fun() -> "Was asked to infer the type of " ^ print_exp e
        ^ " but the type is not inferrable") ;
      raise (Error.Error ("Cannot infer the type of "))
  in
  Debug.deindent ();
  Debug.print(fun() -> "Result of infer for " ^ print_exp e ^ " was " ^ print_exp res) ;
  res

and check_type (sign, cG : signature * ctx) (s : exp) : universe =
  match infer (sign, cG) s with
  | Set n -> n
  | e ->
     Debug.print (fun () -> "Assert universe failed for " ^ print_exp e ^ ".") ;
     raise (Error.Error "Not a universe.")

and check (sign , cG : signature * ctx) (e : exp) (t : exp) : unit =
  Debug.print (fun () ->
      "Check called with: " ^ print_exp e ^ ":" ^ print_exp t ^ " in context: " ^ print_ctx cG);
  Debug.indent();
  begin match e, Whnf.whnf sign t with
  (* checkable terms *)
  | Hole _, _ -> () (* holes are always of the right type *)
  | Fn (fs, e), Pi(tel, t) ->
     let sigma = List.map2 (fun f (_, n, _) -> n, Var f) fs tel in
     let t' = simul_subst sigma t in
     let cG' = simul_subst_on_ctx sigma cG in
     let cGext = List.map2 (fun f (_, _, s) -> f, s) fs (simul_subst_on_tel sigma tel) in
     Debug.indent();
     Debug.print (fun () -> "Checking function: " ^ print_exp (Fn (fs, e)) ^ "\nin context " ^ print_ctx cG ^ ".");
     Debug.print (fun () -> "Resulted in ctx " ^ print_ctx cG'
                            ^ "\nwith extension " ^ print_ctx cGext
                            ^ "\nwith renaming " ^ print_subst sigma ^ ".");
     check (sign, cGext @ cG') e t' ;
     Debug.deindent()

  | _, Box (g, alpha) when is_syntax e ->
    let cP = contextify (sign, cG) g in
    check_syn (sign, cG) cP e alpha

  | _, Ctx when is_syntax e -> check_ctx (sign, cG) e

  | App(h, sp), Box (g, alpha) ->
    check_app (sign, cG) h sp g alpha
    
  | _ ->
     let t' =
       try infer (sign, cG) e
       with Error.Error msg ->
         Debug.print_string msg;
         raise (Error.Error ("Cannot check expression " ^ print_exp e ^ "\n" ^ msg))
     in
     try
       let _, sigma =
         Unify.unify (sign, cG) t t' in
       Debug.print (fun () -> "Unification for " ^ print_exp t ^ " with " ^
                                print_exp t' ^ " succeeded with substitution "
                                ^ Unify.print_subst sigma ^ ".")
     with
     | Unify.Unification_failure prob ->
       let string_e = print_exp e in
       let string_t = print_exp t in
       let string_t' = print_exp t' in
       let message = "Expression: " ^ string_e
                     ^ "\nwas inferred type: " ^ string_t'
                     ^ "\nwhich is not equal to: " ^ string_t ^ " that was checked against."
                     ^ "\nUnification failed with " ^ Unify.print_unification_problem prob
       in
       Debug.print_string message;
       raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))
  end ;
  Debug.deindent();
  Debug.print (fun() -> "Finished check for " ^ print_exp e) ;
  ()

and check_spine (sign, cG) sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
     check (sign, cG) e s ;
     let tel', t' = subst_pi (x, e) tel t in
     check_spine (sign, cG) sp' tel' t'
  | [], [] -> t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      | Pi (tel', t') -> check_spine (sign, cG) sp tel' t'
      | Box (g, SPi (tel', t')) ->
        let cP = contextify (sign, cG) g in
        check_syn_spine (sign, cG) cP sp tel' t'
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ print_exp t))
    end
  | [], _ -> Pi (tel, t)

and check_pi (sign, cG) tel t =
  match tel with
  | [] -> infer (sign, cG) t
  | (_, x, s)::tel' ->
     let us = check_type (sign, cG) s in
     let ut = check_pi (sign, (x, s)::cG) tel' t in
     begin match ut with
     | Set 0 -> Set 0 (* Set 0 is impredicative *)
     | Set n -> Set (max us n)
     | _ -> raise (Error.Error ("Expression " ^ print_exp (Pi(tel,t)) ^ " cannot be checked to be a type."))
     end

(* This function is used because we overload application *)
and check_app (sign, cG) (h : exp) (sp : exp list) (g : exp) (t : exp) : unit =
  let t' =
    match h with
    | Const n ->
      begin match lookup_sign sign n with
      | Pi (tel, t) -> check_spine (sign, cG) sp tel t
      | SPi (tel, t) -> Box(g, check_syn_spine (sign, cG) (contextify (sign, cG) g) sp tel t)
      | t -> raise (Error.Error ("Head of application " ^ print_exp h ^ " had type "
                                 ^ print_exp t ^ " which is not of function type."))
      end
    | Var n ->
      begin match lookup n cG with
      | Pi (tel, t) -> check_spine (sign, cG) sp tel t
      | SPi (tel, t) -> Box (g, check_syn_spine (sign, cG) (contextify (sign, cG) g) sp tel t)
      | t -> raise (Error.Error ("Head of application " ^ print_exp h ^ " had type "
                                 ^ print_exp t ^ " which is not of function type."))
      end
    | _ when is_syntax h ->
      let cP = contextify (sign, cG) g in
      begin match infer_syn (sign, cG) cP h with
      | SPi (tel, t) -> Box (g, check_syn_spine (sign, cG) cP sp tel t)
      | _ -> raise (Error.Error "Term in function position is not of function type")
      end
    | _ -> raise (Error.Error ("Term " ^ print_exp h ^ " cannot by the head of an application."))
  in
  try
       let _, sigma =
       Unify.unify (sign, cG) (Box (g, t)) t' in
       Debug.print (fun () -> "Unification for " ^ print_exp (Box (g, t)) ^ " with " ^
                                print_exp t' ^ " succeeded with substitution "
                                ^ Unify.print_subst sigma ^ ".")
     with
     | Unify.Unification_failure prob ->
       let string_e = print_exp (App (h, sp)) in
       let string_t = print_exp (Box (g, t)) in
       let string_t' = print_exp t' in
       let message = "Expression: " ^ string_e
                     ^ "\nwas inferred type: " ^ string_t'
                     ^ "\nwhich is not equal to: " ^ string_t ^ " that was checked against."
                     ^ "\nUnification failed with " ^ Unify.print_unification_problem prob
       in
       Debug.print_string message;
       raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))
    
    (*     try match infer (sign, cG) h with *)
    (*    | Pi (tel, t) -> *)
    (*      check_spine (sign, cG) sp tel t *)
    (* with  *)


and check_syn_type (sign, cG) cP (e : exp) : unit =
  Debug.print (fun () -> "Checking syntactic type " ^ print_exp e);
  Debug.indent ();
  begin
    match Whnf.whnf sign e with
    | Star -> ()
    | SPi (tel, e') ->
      let rec check_tel_type cP = function
        | [] -> cP
        | (_, x, s) :: tel ->
          check_syn_type (sign, cG) cP s;
          check_tel_type (BSnoc (cP, x, s)) tel
      in
      let cP' = check_tel_type cP tel in
      check_syn_type (sign, cG) cP' e'
    | Const n -> if lookup_syn_def n sign = [] then ()
      else raise (Error.Error ("Type " ^ n ^ " is not fully applied."))
    | App (Const n, es) ->
      let tel = lookup_syn_def n sign in
      begin try
              List.iter2 (fun e (_, x, t) -> check_syn (sign, cG) cP e t) es tel
        with Invalid_argument _ -> raise (Error.Error ("Type " ^ n ^ " is not fully applied."))
      end
    | _ -> raise (Error.Error (print_exp e ^ " is not a syntactic type."))
  end; Debug.deindent ()
    
and check_ctx (sign, cG) g =
  match g with
  | Snoc (g, _, e) ->
    check_ctx (sign, cG) g;
    let cP' = contextify (sign, cG) g in
    check_syn_type (sign, cG) cP' e
  | Nil -> ()
  | Var x ->
    begin match lookup x cG with
    | Ctx -> ()
    | _ -> raise (Error.Error ("Variable " ^ print_name x ^ " was expected to be a context variable."))
    end
  | _ -> raise (Error.Error ("Expression " ^ print_exp g ^ " was expected to be a context."))


and check_syn (sign, cG) cP (e : exp) (t : exp) =
  Debug.print (fun () -> "Checking syntactic expression " ^ print_exp e ^ " against type "
    ^ print_exp t ^ " in bound context " ^ print_bctx cP);
  Debug.indent ();
  begin
    match e, Whnf.whnf sign t with
    | Lam (f, e), SPi (tel, t) ->
      let cP', tel' = bctx_of_lam_stel f tel in
      begin match tel' with
      | [] -> check_syn (sign, cG) (append_bctx cP' cP) e t
      | _ -> check_syn (sign, cG) (append_bctx cP' cP) e (SPi (tel', t))
      end
    | e, t when is_syntax e ->
      Debug.print(fun ()-> "Expression " ^ print_exp e ^ " is syntactic and thus being inferred");
      let t' = infer_syn (sign, cG) cP e in
      let _ = try
          Unify.unify (sign, cG) t t'
      with
        Unify.Unification_failure prob ->
        raise (Error.Error ("Checking syntactic term " ^ print_exp e ^ " against type " ^ print_exp t
                            ^ "\nFailed with unification problem:\n" ^ Unify.print_unification_problem prob))
      in
      ()
    | e, t ->
      Debug.print(fun ()-> "Expression " ^ print_exp e ^ " is not syntactic and thus back to check");
      check (sign, cG) e (Box (decontextify cP, t))
  end; Debug.deindent ()

and infer_syn (sign, cG) cP (e : exp) =
  Debug.print (fun () -> "Inferring type of syntactic expression " ^ print_exp e
    ^ " in bound context " ^ print_bctx cP);
  Debug.indent ();
  let res =
    match e with
    | SPi (tel, t) -> check_spi (sign, cG) cP tel t
    | AppL (e, es) ->
      begin match infer_syn (sign, cG) cP e with
      | SPi (tel, t) -> check_syn_spine (sign, cG) cP es tel t
      | _ -> raise (Error.Error "Term in function position is not of function type")
      end
    | Var x -> check_box (sign, cG) cP (lookup x cG)
    | Const n -> check_box (sign, cG) cP (lookup_sign sign n)
    | BVar i ->
      let t = lookup_bound i cP in
      Debug.print (fun () -> "Looking bound variable " ^ string_of_int i ^ " resulted in type " ^ print_exp t
        ^ "\n Context is " ^ print_bctx cP);
      t
    | Clos (e, s) ->
      let cP' = contextify (sign, cG) (infer_syn (sign, cG) cP s) in
      infer_syn (sign, cG) cP' e
    | EmptyS -> Nil
    | Shift n -> let cP' = drop_suffix cP n in
                 Debug.print(fun () -> "Shift " ^ string_of_int n
                   ^ " bring context " ^ print_bctx cP ^ " to context " ^ print_bctx cP');
                 decontextify cP'
    | Dot (s, e) ->
      let g = infer_syn (sign, cG) cP s in
      let cP' = contextify (sign, cG) g in
      let t = infer_syn (sign, cG) cP' e in
      Snoc (g, "_", t)
    | Comp (s1, s2) ->
      let g1 = infer_syn (sign, cG) cP s1 in
      let cP' = contextify (sign, cG) g1 in
      infer_syn (sign, cG) cP' s2
    | ShiftS s ->
      begin match cP with
      | BNil -> raise (Error.Error ("Shifting a substitution in an empty context"))
      | BSnoc (cP', x, t) ->
        let g = infer_syn (sign, cG) cP' s in
        Snoc (g, x, t)
      | CtxVar x -> raise (Error.Violation ("We're not too sure what to do here"))
      end
    | _ -> raise (Error.Error ("Cannot infer syntactic expression " ^ print_exp e))
  in Debug.deindent (); res

and check_syn_spine (sign, cG) cP sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
    let wrap t = Clos (t, (Dot (Shift 1, e))) in
    check_syn (sign, cG) cP e s;
    let tel' = List.map (fun (i, n, e) -> i, n, wrap e) tel in
    check_syn_spine (sign, cG) cP sp' tel' (wrap t)
  | [], [] -> t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      (* Not sure if Pi's are allowed inside boxes *)
      (* | Pi (tel', t') -> check_spine (sign, cG) sp tel' t' *)
      | SPi (tel', t') -> check_syn_spine (sign, cG) cP sp tel' t
      (* | Box (g, SPi (tel', t')) -> *)
      (*   let cD, sigma, cP' = unify_ctx (sign, cG) g cP in *)
      (*   check_syn_spine (sign, cD) cP' sp (simul_subst_on_stel sigma tel') (simul_subst sigma t') *)
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ print_exp t))
    end
  | [], _ -> SPi (tel, t)

and check_spi (sign, cG) cP tel t =
  match tel with
  | [] -> infer_syn (sign, cG) cP t
  | (_, x, s)::tel' ->
    check_syn_type (sign, cG) cP s;
    check_spi (sign, cG) (BSnoc (cP, x, s)) tel' t

let rec check_tel (sign, cG) u tel =
  match tel with
  | [] -> u
  | (_, x, s) :: tel' ->
     if u = 0 then
       check_tel (sign, (x, s) :: cG) u tel'
     else
       let us = check_type (sign, cG) s in
       let u' = max us u in
       Debug.print (fun () -> "Checking telescope at variable " ^ print_name x
                           ^ " which has universe " ^ print_universe us
                           ^ " upgrading telescope's universe from "
                           ^ print_universe u ^ " to " ^ print_universe u');
       check_tel (sign, (x, s) :: cG) u' tel'

let rec check_stel (sign, cG) cP tel =
  match tel with
  | [] -> ()
  | (_, x, s) :: tel' ->
    check_syn_type (sign, cG) cP s;
    check_stel (sign, cG) (BSnoc (cP, x, s)) tel'

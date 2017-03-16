open Syntax.Int
open Print.Int
open Meta
open Sign
open Name

let is_syntax = function
  | Lam _
  | AppL _
  | App _
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
  | Nil -> true
  | _ -> false

let lookup x cG =
  begin
    try List.assoc x cG
    with Not_found ->
      raise (Error.Violation
               ("Unbound var after preprocessing, this cannot happen. (Var: " ^ print_name x ^ ")"))
  end

let is_ctx (sign, cG) = function
  | Nil
  | Snoc _ -> true
  | Var g when lookup g cG = Ctx -> true
  | _ -> false

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

let unify_ctx (sign, cG) e g cP =
  let g' = decontextify cP in
  Debug.print(fun () -> "Unifying contexts.\ng  = " ^ print_exp g ^ "\ng' = " ^ print_exp g' ^ "\n with ctx " ^ print_ctx cG);
  let cD, sigma =
    try
      Unify.unify (sign, cG) g g'
    with
      Unify.Unification_failure problem ->
        Debug.print (fun () -> Unify.print_unification_problem problem);
        raise (Error.Error (print_exp e ^ " is defined in bound context " ^ print_exp g
                            ^ " but it was expected to be in bound context " ^ print_exp g'))
  in
  cD, sigma


let check_box (sign, cG) cP e = function
  | Box (g, t) ->
    let cD, sigma = unify_ctx (sign, cG) e g cP in
    simul_subst sigma t
  | t -> t

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
       | SPi _ as t ->
         raise (Error.Error ("The left hand side (" ^ print_exp h ^ ") was expected to be of extensional "
                             ^ "function type while it was found to be of intensional function type " ^ print_exp t))
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

    | Ctx -> Set 0
    | Box (g, e) ->
      check_ctx (sign, cG) g;
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
    "Checking " ^ Pretty.print_exp (sign, cG) BNil e ^ "\nagainst "
    ^ Pretty.print_exp (sign, cG) BNil t ^ "\nin context: " ^ print_ctx cG);
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
        check_spi_spine (sign, cG) cP sp tel' t'
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

and check_syn_type (sign, cG) cP (e : exp) : unit =
  Debug.print (fun () -> "Checking syntactic type " ^ print_exp e ^ "\nin context " ^ print_ctx cG);
  Debug.indent ();
  begin
    match e with
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
    | Pi (tel, e') ->
      let rec check_tel_type cG = function
        | [] -> ()
        | (_, x, s) :: tel ->
          check_syn_type (sign, cG) cP s;
          check_tel_type ((x, s) :: cG) tel
      in
      check_tel_type cG tel;
      check_syn_type (sign, cG) cP e'

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
  Debug.print (fun () -> "Checking syntactic expression " ^ Pretty.print_exp (sign, cG) cP e
    ^ "\nagainst type " ^ Pretty.print_exp (sign, cG) cP t ^ "\nin bound context "
    ^ print_bctx cP ^ "\nand context " ^ print_ctx cG);
  Debug.indent ();
  begin
    match e, Whnf.whnf sign t with
    | Lam (f, e), SPi (tel, t) ->
      let cP', tel' = bctx_of_lam_stel f tel in
      begin match tel' with
      | [] -> check_syn (sign, cG) (append_bctx cP' cP) e t
      | _ -> check_syn (sign, cG) (append_bctx cP' cP) e (SPi (tel', t))
      end
    | _, Ctx -> check_ctx (sign, cG) e
    | EmptyS, Nil -> ()
    | Shift n, g when is_ctx (sign, cG) g ->
      let g' = decontextify (drop_suffix cP n) in
      let _ = try Unify.unify (sign, cG) g g'
        with Unify.Unification_failure prob ->
          raise (Error.Error ("Expected context: " ^ print_exp g ^ " shifted by " ^ string_of_int n
                              ^ " position" ^ (if n > 1 then "s" else "")
                              ^".\nFound context: " ^ print_exp g' ^ "\nUnification failed with : "
                              ^ Unify.print_unification_problem prob))
      in ()
    | Dot (s, e), Snoc (g, _, t) ->
      check_syn (sign, cG) cP s g;
      check_syn (sign, cG) cP e (Clos(t, s))
    | Comp (s1, s2), g ->
      raise (Error.Violation "Compositions only appear as the result of whnf which assumes well typed terms")
    | ShiftS s, g ->
      raise (Error.Violation "Substitution shiftings only appear as the result of whnf which assumes well typed terms")
    | e, t when is_syntax e ->
      Debug.print(fun ()-> "Expression " ^ print_exp e ^ " is syntactic and thus being inferred");
      let t' = match infer_syn (sign, cG) cP e with
        | Box (g, t) ->
          let cD, sigma = unify_ctx (sign, cG) t g cP in
          simul_subst sigma t
        | t -> t
      in
      let _ = try
          Unify.unify (sign, cG) t t'
      with
        Unify.Unification_failure prob ->
          raise (Error.Error ("Checking syntactic term " ^ print_exp e ^ " against type " ^ print_exp t
                              ^ "\nIn context " ^ print_bctx cP
                            ^ "\nFailed with unification problem:\n" ^ Unify.print_unification_problem prob))
      in
      ()
    | e, t ->
      Debug.print(fun ()-> "Expression " ^ print_exp e ^ " is not syntactic and thus back to check");
      check (sign, cG) e (Box (decontextify cP, t))
  end; Debug.deindent ()

and infer_syn (sign, cG) cP (e : exp) =
  Debug.print (fun () -> "Inferring type of syntactic expression " ^ print_exp e
    ^ "\nin bound context " ^ print_bctx cP ^ "\nand context " ^ print_ctx cG);
  Debug.indent ();
  let res =
    match e with
    | SPi (tel, t) -> check_spi (sign, cG) cP tel t
    | App (e, es) ->
      begin match infer_syn (sign, cG) cP e with
      | Pi (tel, t) -> check_syn_spine (sign, cG) cP es tel t
      | _ -> raise (Error.Error "Term in function position is not of function type")
      end

    | AppL (e, es) ->
      begin match Whnf.whnf sign (infer_syn (sign, cG) cP e) with
      | SPi (tel, t) -> check_spi_spine (sign, cG) cP es tel t
      | t -> raise (Error.Error ("Term in function position is not of function type. Instead " ^ print_exp t))
      end
    | Var x ->
      Debug.print (fun () -> "Variable " ^ print_name x ^ " is being looked up in context " ^ print_ctx cG);
      check_box (sign, cG) cP e (lookup x cG)
    | Const n -> check_box (sign, cG) cP e (lookup_sign sign n)
    | BVar i ->
      let t = lookup_bound i cP in
      Debug.print (fun () -> "Looking bound variable " ^ string_of_int i ^ " resulted in type " ^ print_exp t
        ^ "\n Context is " ^ print_bctx cP);
      Clos(t, Shift (i+1))
    (* | Clos (Var x, s) -> *)
    (*   Debug.print(fun () -> "Hello I am a clos on a var"); *)
    (*   begin match lookup x cG with *)
    (*   | Box (g, t) -> *)
    (*     let g' = infer_syn (sign, cG) cP s in *)
    (*     Debug.print (fun () -> "Infer_syn: Clos-var -- infered " ^ print_exp g' ^ " for substitution "^ print_exp s); *)
    (*     check_ctx (sign, cG) g'; *)
    (*     let cP1 = contextify (sign, cG) g in *)
    (*     let cP2 = contextify (sign, cG) g' in *)
    (*     let rec unify_ctx cP1 cP2 s = match cP1, cP2, s with *)
    (*       | BNil, BNil, _ -> [], Shift 0 *)
    (*       | CtxVar x, CtxVar y, _ when x = y -> [], Shift 0 *)
    (*       | BSnoc(cP1', _, t1), BSnoc(cP2', _, t2), Dot(s', e) -> *)
    (*         let sigma, s0 = unify_ctx cP1' cP2' s' in *)
    (*         let _, sigma' = Unify.unify (sign, cG) (Clos (simul_subst sigma t1, s0)) (Clos (simul_subst sigma t2, s0)) in *)
    (*         sigma @ sigma', simul_subst sigma (Dot (s0, e)) *)
    (*       | _, _, _ -> *)
    (*         let g1 = decontextify cP1 in *)
    (*         let g2 = decontextify cP2 in *)
    (*         let _, sigma = Unify.unify (sign, cG) g1 g2 in *)
    (*         sigma, Shift 0  *)
    (*     in *)
    (*     let sigma, _ = unify_ctx cP1 cP2 s in *)
    (*     simul_subst sigma t *)
    (*   | t -> t *)
    (*   end *)
    | Clos (e, s) ->
      begin
        let t = try infer (sign, cG) e
          with Error.Error msg ->
            Debug.print (fun () -> "Inferring " ^ print_exp e ^ " returned message:\n" ^ msg);
            raise (Error.Error ("The left hand side of the closure " ^ print_exp (Clos (e, s)) ^ " was not inferrable."))
        in
        match t with
        | Box(g, t) ->
          check_syn (sign, cG) cP s g;
          Clos(t, s)
        | _ -> raise (Error.Error ("Expected " ^ print_exp e ^ " to be of boxed type. Instead inferred type " ^ print_exp t))
      end
    | _ -> raise (Error.Error ("Cannot infer syntactic expression " ^ print_exp e))
  in Debug.deindent (); res

and check_syn_spine (sign, cG) cP sp tel t =
  Debug.print (fun () -> "Checking syn spine:\nsp = " ^ print_exps sp ^ "\ntel = " ^ print_tel tel);
  Debug.indent ();
  let res = match sp, tel with
    | e::sp', (_, x, s)::tel ->
      begin match Whnf.whnf sign s with
        | Box(g, s) ->
          check_syn (sign, cG) (contextify (sign, cG) g) e s
          (* let cD, sigma = unify_ctx (sign, cG) s g cP in *)
          (* simul_subst sigma s *)
        | s -> check_syn (sign, cG) cP e s
      end;
      Debug.print (fun () -> "Checking syn spine:\ne = " ^ print_exp e ^ "\ns = " ^ print_exp s);
      let tel', t' = subst_pi (x, e) tel t in
      check_syn_spine (sign, cG) cP sp' tel' t'
  | [], [] -> t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      | Pi (tel', t') -> check_syn_spine (sign, cG) cP sp tel' t'
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ print_exp t))
    end
  | [], _ -> Pi (tel, t)
  in
  Debug.deindent ();
  res

and check_spi_spine (sign, cG) cP sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
    let wrap t = Clos (t, (Dot (Shift 1, e))) in
    check_syn (sign, cG) cP e s;
    let tel' = List.map (fun (i, n, e) -> i, n, wrap e) tel in
    check_spi_spine (sign, cG) cP sp' tel' (wrap t)
  | [], [] -> t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      (* Not sure if Pi's are allowed inside boxes *)
      (* | Pi (tel', t') -> check_spine (sign, cG) sp tel' t' *)
      | SPi (tel', t') -> check_spi_spine (sign, cG) cP sp tel' t
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

let rec check_syn_tel (sign, cG) tel =
  match tel with
  | [] -> ()
  | (_, x, s) :: tel' ->
    check_syn_type (sign, cG) BNil s;
    check_syn_tel (sign, (x, s) :: cG) tel'

let rec check_stel (sign, cG) cP tel =
  match tel with
  | [] -> ()
  | (_, x, s) :: tel' ->
    check_syn_type (sign, cG) cP s;
    check_stel (sign, cG) (BSnoc (cP, x, s)) tel'

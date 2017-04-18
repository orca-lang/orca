open Meta
open MetaSub
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

let compute_wkn (sign, cG) cP cP' =
  let listify cP =
    let rec listify' = function
      | I.Nil -> None, []
      | I.CtxVar g -> Some g, []
      | I.Snoc (cP, x, t) ->
         let b, ts = listify' cP in
         b, (x,t)::ts
    in
    let b, ts = listify' cP in
    b, List.rev ts
  in
  let b1, ts1 = listify cP in
  let b2, ts2 = listify cP' in
  if b1 = b2 then
    let rec check_lists ts1 ts2 cP =
      match ts1, ts2 with
      | xs, [] -> I.Shift (List.length xs)
      | (n,x)::xs, (_,y)::ys ->
         let _, sigma = try
             Unify.unify_syn (sign, cG) cP x y
           with Unify.Unification_failure problem ->
             Debug.print (fun () -> Unify.print_unification_problem problem);
             raise (Error.Error ("Types in contexts cannot unify"))
         in
         check_lists xs ys (I.Snoc(cP, n, simul_subst_syn sigma x))
      | _ -> raise (Error.Error "Term cannot be of larger context than ambiant one")
    in
    let cP1 = match b1 with
      | None -> I.Nil
      | Some g -> I.CtxVar g
    in
    check_lists ts1 ts2 cP1
  else
    raise (Error.Error ("Cannot infer the substitution"))




  (* Debug.print(fun () -> "Unifying contexts.\ng  = " ^ IP.print_exp g ^ "\ng' = " ^ IP.print_exp g' ^ "\n with ctx " ^ IP.print_ctx cG); *)
  (* let cD, sigma = *)
    (* try *)
    (*   Unify.unify_bctx (sign, cG) cP cP' *)
    (* with *)
    (*   Unify.Unification_failure problem -> *)
    (*     Debug.print (fun () -> Unify.print_unification_problem problem); *)
    (*     raise (Error.Error (IP.print_exp e ^ " is defined in bound context " ^ IP.print_bctx cP *)
    (*                         ^ " but it was expected to be in bound context " ^ IP.print_bctx cP')) *)

(* let check_box (sign, cG) cP e = function *)
(*   | I.Box (g, t) -> *)
(*     let cD, sigma = unify_ctx (sign, cG) e g cP in *)
(*     simul_subst sigma e, simul_subst_syn sigma t *)
(*   | t -> e, t *)



(* infers the type and returns the internal term and its type *)
let rec infer (sign, cG : signature * I.ctx) (e : A.exp) : I.exp * I.exp =
  Debug.print (fun () -> "Infer called with: " ^ AP.print_exp e ^ " in context: " ^ IP.print_ctx cG);
  Debug.indent() ;
  let res_e, res_t  =
    match e with
    | A.Annot (e, t) ->
       let t', _ = infer_type (sign, cG) t in
       check (sign, cG) e t', t'
    | A.Const n ->
       I.Const n, lookup_sign sign n
    | A.Var n -> I.Var n, lookup_ctx_fail cG n
    | A.App (h, sp) ->
      begin match infer (sign, cG) h with
       | h', I.Pi (tel, t) ->
          let sp', spA, t' = check_spine (sign, cG) sp tel t in
          let nh = I.App (h', sp') in
          if spA = [] then
            nh, t'
          else
            begin match t' with
            | I.Box (cP, t) ->
               begin match Whnf.rewrite sign cP t with
               | I.SPi (tel, t) ->
                  let sp'', t'' = check_syn_spine (sign, cG) cP spA tel t in
                  I.TermBox(cP, I.AppL(I.Unbox(nh, I.id_sub, cP), sp'')), I.Box (cP, t'')
               | _ -> raise (Error.Error ("Too many parameters for the type"))
               end
            | _ -> raise (Error.Error "Extra parameters non consumed")
            end
       | _, t -> raise (Error.Error ("The left hand side (" ^ AP.print_exp h ^ ") of the application was of type "
                                  ^ IP.print_exp t ^ " which is not of function type"))
       end
    | A.Set n -> I.Set n, I.Set (n + 1)
    | A.Pi (tel, t) ->
       check_pi (sign, cG) tel t

    | A.Ctx -> I.Ctx, I.Set 0
    | A.Box (g, e) ->
      let cP = check_ctx (sign, cG) g in
      let e' = check_syn_type (sign, cG) cP e in
      I.Box(cP, e'), I.Set 0

    | _ ->
      Debug.print (fun() -> "Was asked to infer the type of " ^ AP.print_exp e
        ^ " but the type is not inferrable") ;
      raise (Error.Error ("Cannot infer the type of "))
  in
  Debug.deindent ();
  Debug.print(fun() -> "Result of infer for " ^ AP.print_exp e ^ " was " ^ IP.print_exp res_t) ;
  res_e, res_t

and infer_type (sign, cG : signature * I.ctx) (s : A.exp) : I.exp * I.universe =
  match infer (sign, cG) s with
  | t, I.Set n -> t, n
  | t, e ->
     Debug.print (fun () -> "Assert universe failed for " ^ IP.print_exp e ^ ".") ;
     raise (Error.Error "Not a universe.")

and check (sign , cG : signature * I.ctx) (e : A.exp) (t : I.exp) : I.exp =
  Debug.print (fun () ->
      "Checking " ^ AP.print_exp e ^ "\nagainst "
      ^ Pretty.print_exp cG t ^ "\nin context: " ^ IP.print_ctx cG);
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
       Debug.print (fun () -> "Checking function: " ^ AP.print_exp (A.Fn (fs, e)) ^ "\nin context " ^ IP.print_ctx cG ^ ".");
       Debug.print (fun () -> "Resulted in ctx " ^ IP.print_ctx cG'
                              ^ "\nwith extension " ^ IP.print_ctx cGext
                              ^ "\nwith renaming " ^ IP.print_subst sigma ^ ".");
       let e' = check (sign, cGext @ cG') e t' in
       Debug.deindent() ;
       I.Fn (fs, e')

    | _, I.Box (cP, alpha) when is_syntax e ->
       I.TermBox (cP, check_syn (sign, cG) cP e alpha)

    | _, I.Ctx when is_syntax e -> I.BCtx (check_ctx (sign, cG) e)

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
                                  ^ print_subst sigma ^ ".");
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
     let sp', spA, t'' = check_spine (sign, cG) sp' tel' t' in
     e'::sp', spA, t''
  | [], [] -> [], [], t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      | I.Pi (tel', t') -> check_spine (sign, cG) sp tel' t'
      | t -> [], sp, t          (* The rest of the parameters must be AppL *)
    end
  | [], _ -> [], [], I.Pi (tel, t)

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

and check_syn_type (sign, cG) cP (e : A.exp) : I.syn_exp =
  Debug.print (fun () -> "Checking syntactic type " ^ AP.print_exp e
                         ^ "\nin context " ^ IP.print_ctx cG);
  Debug.indent ();
  let res =
    match e with
    | A.Star -> I.Star
    | A.SPi (tel, e') ->
      let rec check_stel_type cP = function
        | [] -> [], cP
        | (i, x, s) :: tel ->
           let s' = check_syn_type (sign, cG) cP s in
           let tel', cP' = check_stel_type (I.Snoc (cP, x, s')) tel in
          (i, x, s') :: tel', cP'
      in
      let tel', cP' = check_stel_type cP tel in
      I.SPi (tel', check_syn_type (sign, cG) cP' e')
    | A.Const n -> if lookup_syn_def sign n = [] then I.SConst n
      else raise (Error.Error ("Type " ^ n ^ " is not fully applied."))
    | A.App (A.Const n, es) ->
      let tel = lookup_syn_def sign n in
      begin try
          I.AppL (I.SConst n, List.map2 (fun e (_, x, t) -> check_syn (sign, cG) cP e t) es tel)
        with Invalid_argument _ -> raise (Error.Error ("Type " ^ n ^ " is not fully applied."))
      end
    | _ -> raise (Error.Error (AP.print_exp e ^ " is not a syntactic type."))
  in Debug.deindent (); res

and check_ctx (sign, cG) g =
  match g with
  | A.Snoc (g, x, e) ->
    let cP = check_ctx (sign, cG) g in
    I.Snoc (cP, x, check_syn_type (sign, cG) cP e)
  | A.Nil -> I.Nil
  | A.Var x ->
    begin match lookup_ctx_fail cG x with
    | I.Ctx -> I.CtxVar x
    | _ -> raise (Error.Error ("Variable " ^ print_name x ^ " was expected to be a context variable."))
    end
  | _ -> raise (Error.Error ("Expression " ^ AP.print_exp g ^ " was expected to be a context."))


and check_syn (sign, cG) cP (e : A.exp) (t : I.syn_exp) =
  Debug.print (fun () -> "Checking syntactic expression " ^ AP.print_exp e
    ^ "\nagainst type " ^ Pretty.print_syn_exp cG cP t ^ "\nin bound context "
    ^ IP.print_bctx cP ^ "\nand context " ^ IP.print_ctx cG);
  Debug.indent ();
  let res =
    match e, Whnf.rewrite sign cP t with
    | A.Lam (fs, e), I.SPi (tel, t) ->
       let cP', tel' = bctx_of_lam_stel fs tel cP in
       let rec lam_tel fs tel =
         begin match fs, tel with
         | x::xs, (_,_,t)::tel' -> (x, t) :: lam_tel xs tel'
         | [], _ -> []
         | _, [] -> raise (Error.Violation "It's a violation; the error was already raised (there).")
         end
       in
       let fs' = lam_tel fs tel in
       begin match tel' with
       | [] -> I.Lam (fs', check_syn (sign, cG) cP' e t)
       | _ -> I.Lam (fs', check_syn (sign, cG) cP' e (I.SPi (tel', t)))
       end

    | _, I.SCtx -> I.SBCtx(check_ctx (sign, cG) e)
    | A.EmptyS, I.SBCtx I.Nil -> I.Empty
    | A.Shift n, I.SBCtx cP' ->
      let cP'' = drop_suffix cP n in
      let _ = try Unify.unify_bctx (sign, cG) cP' cP''
        with Unify.Unification_failure prob ->
          raise (Error.Error ("Expected context: " ^ IP.print_bctx cP ^ " shifted by " ^ string_of_int n
                              ^ " position" ^ (if n > 1 then "s" else "")
                              ^".\nFound context: " ^ IP.print_bctx cP' ^ "\nUnification failed with : "
                              ^ Unify.print_unification_problem prob))
      in I.Shift n
    | A.Dot (s, e), I.SBCtx (I.Snoc (cP', _, t)) ->
      let s' = check_syn (sign, cG) cP s (I.SBCtx cP') in
      I.Dot (s', check_syn (sign, cG) cP e (I.Clos(t, s', cP')))
    | e, t when is_syntax e ->
      Debug.print(fun ()-> "Expression " ^ AP.print_exp e ^ " is syntactic and thus being inferred");
      let e', t' = match infer_syn (sign, cG) cP e with
        | e, t -> e, t
      in
      let _, sigma = try
          Unify.unify_syn (sign, cG) cP t t'
      with
        Unify.Unification_failure prob ->
          raise (Error.Error ("Checking syntactic term " ^ AP.print_exp e ^ " against type " ^ IP.print_syn_exp t
                              ^ "\nIn context " ^ IP.print_bctx cP
                            ^ "\nFailed with unification problem:\n" ^ Unify.print_unification_problem prob))
      in
      simul_subst_syn sigma e'
    | e, t ->
      Debug.print(fun ()-> "Expression " ^ AP.print_exp e ^ " is not syntactic and thus back to check");
      let e' = check (sign, cG) e (I.Box (cP, t)) in
      I.Unbox (e', I.id_sub, cP)
  in Debug.deindent (); res

and infer_syn (sign, cG) cP (e : A.exp) =
  Debug.print (fun () -> "Inferring type of syntactic expression " ^ AP.print_exp e
    ^ "\nin bound context " ^ IP.print_bctx cP ^ "\nand context " ^ IP.print_ctx cG);
  Debug.indent ();
  let res =
    match e with
    | A.SPi (tel, t) ->
       let tel', t' = check_spi (sign, cG) cP tel t in
       I.SPi (tel', t'), I.Star
    (* App of Spi type get translated to AppL *)
    | A.App (e, es) ->
      begin match infer_syn (sign, cG) cP e with
      | e', I.SPi (tel, t) ->
         let es', t' = check_syn_spine (sign, cG) cP es tel t in
         I.AppL (e', es'), t'
      | e', t -> raise (Error.Error ("Term " ^ AP.print_exp e
                                     ^ " in function position is not of function type. Instead:\n" ^ IP.print_syn_exp t))
      end

    | A.AppL (e, es) ->
       let e', t' = infer_syn (sign, cG) cP e in
      begin match Whnf.rewrite sign cP t' with
      | I.SPi (tel, t) ->
         let es', t' = check_syn_spine (sign, cG) cP es tel t in
         I.AppL(e', es'), t'
      | t -> raise (Error.Error ("Term in function position is not of function type. Instead " ^ IP.print_syn_exp t))
      end

    | A.Var x ->
       Debug.print (fun () -> "Variable " ^ print_name x ^ " is being looked up in context " ^ IP.print_ctx cG);
       begin match lookup_ctx_fail cG x with
       | I.Box(cP', t') ->
          let sigma = compute_wkn (sign, cG) cP cP' in
          I.Unbox(I.Var x, sigma, cP'),  I.Clos(t', sigma, cP')
       | t -> raise (Error.Error ("Expected a box type, got " ^ IP.print_exp t))
       end
    | A.Const n when is_syn_con sign n ->
       I.SConst n, lookup_syn_sign sign n

    | A.Const n -> raise (Error.Error ("Constructor " ^ n ^ " was used where a syntactic type was expected."))

    | A.BVar i ->
       let t = lookup_bound cP i in
       Debug.print (fun () -> "Looking bound variable " ^ string_of_int i ^ " resulted in type " ^ IP.print_syn_exp t
                              ^ "\n Context is " ^ IP.print_bctx cP);
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
        | I.Box(cP', t) ->
          let s' = check_syn (sign, cG) cP s (I.SBCtx cP') in
          I.Unbox (e', s', cP'), I.Clos(t, s', cP')
        | _ -> raise (Error.Error ("Expected " ^ AP.print_exp e ^ " to be of boxed type. Instead inferred type " ^ IP.print_exp t))
      end
    | _ -> raise (Error.Error ("Cannot infer syntactic expression " ^ AP.print_exp e))
  in Debug.deindent (); res

and check_syn_spine (sign, cG) cP sp tel t =
  Debug.print (fun () -> "Checking syn spine:\nsp = " ^ AP.print_exps sp
                         ^ "\ntel = " ^ IP.print_stel tel);
  Debug.indent ();
  let rec check_spine sp tel t sl cP' =
    let sigma = List.fold_right (fun x sigma -> I.Dot(sigma, x)) sl (I.Shift (List.length sl)) in
    match sp, tel with
    | e::sp', (_, x, s)::tel ->
       let e' = check_syn (sign, cG) cP e (I.Clos (s, sigma, cP')) in
       let sp'', t' = check_spine sp' tel t (e' :: sl) (I.Snoc(cP', x, s)) in
       e'::sp'', t'
    | [], [] -> [], I.Clos(t, sigma, cP')
    | _, [] ->
       begin
         match Whnf.rewrite sign cP (I.Clos (t, sigma, cP')) with
         | I.SPi (tel', t') -> check_spine sp tel' t [] cP'
         | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ IP.print_syn_exp t))
       end
    | [], _ -> [], I.SPi (tel, t)
  in
  let res = check_spine sp tel t [] cP in
  Debug.deindent ();
  res

and check_spi (sign, cG) cP (tel : A.stel) t =
  match tel with
  | [] -> [], check_syn_type (sign, cG) cP t
  | (i, x, s)::tel' ->
     let s' = check_syn_type (sign, cG) cP s in
     let tel'', t' = check_spi (sign, cG) (I.Snoc (cP, x, s')) tel' t in
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


let rec check_stel (sign, cG) cP tel =
  match tel with
  | [] -> []
  | (i, x, s) :: tel' ->
    let s' = check_syn_type (sign, cG) cP s in
    (i, x, s'):: (check_stel (sign, cG) (I.Snoc (cP, x, s')) tel')

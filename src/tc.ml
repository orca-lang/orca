open Syntax
open Syntax.Int
open Print.Int
open Sign
open Meta
open Name
open TCTools

module P = Pretty

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
  | Dot _
  | Snoc _
  | Nil -> true
  | _ -> false


let check_box (sign, cG) cP e = function
  | Box (g, t) ->
    let cD, sigma = assert false in (* unify_ctx (sign, cG) e g cP in  *)
    simul_subst sigma t
  | t -> t

let rec check (sign, cG : signature * ctx) e t =
  match e, Whnf.whnf sign t with
  | Hole n, t -> ()
  | Fn(fs, e), Pi(tel, t) ->
     let sigma = List.map2 (fun f (_, n, _) -> n, Var f) fs tel in
       let t' = simul_subst sigma t in
       let cG' = simul_subst_on_ctx sigma cG in
       let cGext = List.map2 (fun f (_, _, s) -> f, s) fs (simul_subst_on_tel sigma tel) in
       check (sign, cGext @ cG') e t'

    | _, Box (g, alpha) when is_syntax e ->
       let cP = contextify (sign, cG) g in
       check_syn (sign, cG) cP e alpha

    | _, Ctx when is_syntax e ->
       check_ctx (sign, cG) e

    | _ ->
       let t' =
         try infer (sign, cG) e
         with Error.Error msg ->
           raise (Error.Error ("Cannot check expression " ^ print_exp e ^ "\n" ^ msg))
       in
       try
         let _ = Unify.unify (sign, cG) t t' in
         ()
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
          raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))

and check_ctx (sign, cG) g =
  match g with
  | Snoc (g, x, e) ->
    check_ctx (sign, cG) g ;
    let cP' = contextify (sign, cG) g in
    check_syn_type (sign, cG) cP' e ;
    ()
  | Nil -> ()
  | Var x ->
    begin match lookup_ctx_fail cG x with
    | Ctx -> ()
    | _ -> raise (Error.Error ("Variable " ^ print_name x ^ " was expected to be a context variable."))
    end
  | _ -> raise (Error.Error ("Expression " ^ print_exp g ^ " was expected to be a context."))

and check_syn (sign, cG) cP e t =
    match e, Whnf.whnf sign t with
    | Lam (f, e), SPi (tel, t) ->
       let cP', tel' = bctx_of_lam_stel f tel cP in
       begin match tel' with
       | [] -> check_syn (sign, cG) cP' e t
       | _ -> check_syn (sign, cG) cP' e (SPi (tel', t))
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
      in
      ()
    | Dot (s, e), Snoc (g, _, t) ->
      check_syn (sign, cG) cP s g ;
      check_syn (sign, cG) cP e (Clos(t, s))
    | e, t when is_syntax e ->
      let t' = match infer_syn (sign, cG) cP e with
        | Box (g, t) ->
          let cD, sigma = assert false (* unify_ctx (sign, cG) t g cP in *) in
          simul_subst sigma t
        | t -> t
      in
      let _, _sigma = try
          Unify.unify (sign, cG) t t'
      with
        Unify.Unification_failure prob ->
          raise (Error.Error ("Checking syntactic term " ^ print_exp e ^ " against type " ^ print_exp t
                              ^ "\nIn context " ^ print_bctx cP
                            ^ "\nFailed with unification problem:\n" ^ Unify.print_unification_problem prob))
      in
      ()
    | e, t ->
      check (sign, cG) e (Box (decontextify cP, t))

and check_syn_type (sign, cG) cP e =
  match e with
    | Star -> ()
    | SPi (tel, e') ->
      let rec check_stel_type cP = function
        | [] -> cP
        | (i, x, s) :: tel ->
           check_syn_type (sign, cG) cP s ;
           check_stel_type (BSnoc (cP, x, s)) tel
      in
      let cP' = check_stel_type cP tel in
      check_syn_type (sign, cG) cP' e

    | Pi (tel, e') ->
      let rec check_tel_type cG = function
        | [] -> ()
        | (i, x, s) :: tel ->
           check_syn_type (sign, cG) cP s ;
           check_tel_type ((x, s) :: cG) tel
      in
      check_tel_type cG tel ;
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

and infer (sign, cG : signature * ctx) (e : exp) : exp =
    match e with
    | Annot (e, t) ->
       let _ = infer_type (sign, cG) t in
       check (sign, cG) e t;
       t
    | Const n -> lookup_sign sign n
    | Var n -> lookup_ctx_fail cG n
    | App (h, sp) ->
      begin match infer (sign, cG) h with
       | Pi (tel, t) ->
          let t' = check_spine (sign, cG) sp tel t in
          t'


       | SPi _ as t ->
         raise (Error.Error ("The left hand side (" ^ print_exp h ^ ") was expected to be of extensional "
                             ^ "function type while it was found to be of intensional function type " ^ print_exp t))

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
      raise (Error.Error ("Cannot infer the type of "))









and infer_syn (sign, cG) cP (e : exp) : exp =
    match e with
    | SPi (tel, t) ->
       check_spi (sign, cG) cP tel t ;
       Star
    | App (e, es) ->
      begin match infer_syn (sign, cG) cP e with
      | Pi (tel, t) ->
         check_syn_spine (sign, cG) cP es tel t
      | _ -> raise (Error.Error "Term in function position is not of function type")
      end

    | AppL (e, es) ->
       let t' = infer_syn (sign, cG) cP e in
       begin match Whnf.whnf sign t' with
       | SPi (tel, t) ->
          check_spi_spine (sign, cG) cP es tel t
      | t -> raise (Error.Error ("Term in function position is not of function type. Instead " ^ print_exp t))
      end
    | Var x -> check_box (sign, cG) cP (Var x) (lookup_ctx_fail cG x)
    | Const n -> check_box (sign, cG) cP (Const n) (lookup_sign sign n)
    | BVar i -> lookup_bound i cP
    | Clos (e, s) ->
      begin
        let t = try infer (sign, cG) e
          with Error.Error msg ->
            raise (Error.Error ("Unable to infer the left hand side of the closure " ^ print_exp (Clos (e, s))
                                ^ "\nbecause " ^ msg ^"."))
        in
        match t with
        | Box(g, t) ->
           check_syn (sign, cG) cP s g ;
           Clos(t, s)
        | _ -> raise (Error.Error ("Expected " ^ print_exp e ^ " to be of boxed type. Instead inferred type " ^ print_exp t))
      end
    | _ -> raise (Error.Error ("Cannot infer syntactic expression " ^ print_exp e))

and check_syn_spine (sign, cG) cP sp tel t =
  let res = match sp, tel with
    | e::sp', (_, x, s)::tel ->
      begin match Whnf.whnf sign s with
        | Box(g, s) ->
           (* we forget about cP and go on with g... MMMM *)
           check_syn (sign, cG) (contextify (sign, cG) g) e s
        | s -> check_syn (sign, cG) cP e s
      end ;
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

  res

and infer_type (sign, cG : signature * ctx) (s : exp) : Syntax.Int.universe =
  match infer (sign, cG) s with
  | Set n -> n
  | e -> raise (Error.Error "Not a universe.")

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
  | (i, x, s)::tel' ->
     let us = infer_type (sign, cG) s in
     let ut = check_pi (sign, (x, s)::cG) tel' t in
     begin match ut with
     | Set 0 -> Set 0 (* Set 0 is impredicative *)
     | Set n -> Set (max us n)
     | _ -> raise (Error.Error ("Expression " ^ print_exp (Pi(tel,t)) ^ " cannot be checked to be a type."))
     end

and check_spi_spine (sign, cG) cP sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
    check_syn (sign, cG) cP e s ;
    let wrap t = Clos (t, (Dot (Shift 1, e))) in
    let tel' = List.map (fun (i, n, e) -> i, n, wrap e) tel in
    check_spi_spine (sign, cG) cP sp' tel' (wrap t)
  | [], [] -> t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      (* Not sure if Pi's are allowed inside boxes *)
      (* | Pi (tel', t') -> check_spine (sign, cG) sp tel' t' *)
      | SPi (tel', t') -> check_spi_spine (sign, cG) cP sp tel' t
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ print_exp t))
    end
  | [], _ -> SPi (tel, t)

and check_spi (sign, cG) cP (tel : stel) t =
  match tel with
  | [] -> check_syn_type (sign, cG) cP t
  | (i, x, s)::tel' ->
     check_syn_type (sign, cG) cP s;
     check_spi (sign, cG) (BSnoc (cP, x, s)) tel' t

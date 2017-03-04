open Syntax.Int
open Sign
open Name

let max_universe (u1 : universe) (u2 : universe) : universe =
  match u1, u2 with
  | Set n, Set n' -> Set (max n n')
  | Star, u -> u
  | u, Star -> u

(* <= for universes *)
let le_universe (u1 : universe) (u2 : universe) : bool =
  match u1, u2 with
  | Set n, Set n' -> n <= n'
  | Star, _ -> true
  | _, Star -> false

let is_syntax = function
  | Lam _
  | AppL _
  | Const _
  | Var _
  | BVar _
  | Clos _
  | EmptyS
  | Shift _
  | Dot _
  | Snoc _
  | Nil
  | Under -> true
  | _ -> false

let drop_suffix cP n =
  if List.length cP < n then
    raise (Error.Error ("Shifted too far"))
  else
    let rec drop cP n =
      match cP, n with
      | _, 0 -> cP
      | _::cP', n -> drop cP' (n-1)
      | _ -> raise (Error.Violation "move on, there's nothing to see here!")
    in
    drop cP n

let rec contextify sign (g : exp) =
  match Whnf.whnf sign g with
  | Nil -> []
  | Snoc (g', x, e) ->
    let cP = contextify sign g' in
    (* is_syn_type (sign, cG) cP e; *)
    (x, e) :: cP
  | _ -> raise (Error.Error ("Expected context, obtained " ^ print_exp g))

let rec decontextify cP =
  match cP with
  | [] -> Nil
  | (x, e) :: cP' -> Snoc (decontextify cP', x, e)
    
let lookup_sign sign cP n =
  match lookup_sign_entry n sign with
  | Definition (_, [], t, _) -> t
  | Definition (_, tel, t, _) -> Pi(tel, t)

  | DataDef (_, ps, is, u) ->
     let tel = ps @ is in
     if Util.empty_list tel
     then Univ u
     else Pi (tel, Univ u)
  | SynDef (_, tel) ->
     if Util.empty_list tel
     then Box (decontextify cP, SStar)
     else Box (decontextify cP, SPi (tel, SStar))
  | Constructor (_, is, (n', pes)) ->
     let t =
       if Util.empty_list pes then
         Const n'
       else
         App (Const n', pes)
     in
     let t' =
       if Util.empty_list is then t else Pi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_exp t');
     t'
  | SConstructor (_, is, (n', pes)) ->
     let t =
       if Util.empty_list pes then
         Const n'
       else
         App (Const n', pes)
     in
     let t' =
       if Util.empty_list is then t else SPi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_exp t');
     Box (decontextify cP, t')

  | Program (_,tel,t, _) -> if tel = [] then t else Pi (tel, t)


let unify_ctx (sign, cG) g cP =
  let g' = decontextify cP in
  let cD, sigma = Unify.unify (sign, cG) g g' in
  let cP' = contextify sign (subst_list sigma g) in
  cD, sigma, cP'
    
let lookup x cG =
  begin
    try List.assoc x cG
    with Not_found ->
      raise (Error.Violation
               ("Unbound var after preprocessing, this cannot happen. (Var: " ^ print_name x ^ ")"))
  end

let lookup_bound i  cP =
  try snd (List.nth cP i)
  with _ -> raise (Error.Error ("Bound variable had index larger than bound context"))

let rec compare_ctxs (sign, cG) cP cP' =
  match cP, cP' with
  | [], [] -> true
  | (_,t)::cP, (_,t')::cP' ->
    let r = try
              let _ = Unify.unify_flex (sign, cG) [] t t' in true
      with
      | _ -> false
    in
    r && compare_ctxs (sign, cG) cP cP'
  | _ -> raise (Error.Error ("cP's are of different lengths"))

let check_box (sign, cG) cP = function
      | Box (g, t) ->
        let cP' = contextify sign g in
        if compare_ctxs (sign, cG) cP cP'
        then t
        else raise (Error.Error "Wrong contexts. Tip: use a substitution?")
      | _ -> raise (Error.Error "Not a box. Don't think outside of the box.")

let rec infer (sign, cG : signature * ctx) cP (e : exp) : exp =
  Debug.print (fun () -> "Infer called with: " ^ print_exp e ^ " in context: " ^ print_ctx cG);
  Debug.indent() ;
  let res =
    match e with
    | Annot (e, t) ->
       check (sign, cG) cP e t ; t
    | Const n ->
       lookup_sign sign cP n
    | Var n -> lookup n cG
    | App (h, sp) ->
       begin match infer (sign, cG) cP h with
       | Pi (tel, t) ->
         check_spine (sign, cG) cP sp tel t
       | SPi (tel, t) ->
         check_syn_spine (sign, cG) cP sp tel t
       | Box (g, SPi (tel, t)) ->
         let cD, sigma, cP' = unify_ctx (sign, cG) g cP in
         Box (g, check_syn_spine (sign, cD) cP' sp (subst_list_on_stel sigma tel) (subst_list sigma t))
       | t -> raise (Error.Error ("The left hand side (" ^ print_exp h ^ ") of the application was of type "
                                  ^ print_exp t ^ " which is not of function type"))
       end

    | Univ u -> Univ (infer_universe u)
    | Pi (tel, t) ->
       check_pi (sign, cG) cP tel t

    | Box (g, e) ->
      check (sign, cG) cP g Ctx;
      let cD, sigma, cP' = unify_ctx (sign, cG) g cP in
      check_syn_type (sign, cD) cP' (subst_list sigma e);
      Univ Star

    | _ ->
      try
        let t = infer_syn (sign, cG) cP e in
        Box (decontextify cP, t)
      with Error.Error _ -> 
         Debug.print (fun() -> "Was asked to infer the type of " ^ print_exp e
                               ^ " but the type is not inferrable") ;
         raise (Error.Error "Cannot infer the type of this expression")
  in
  Debug.deindent ();
  Debug.print(fun() -> "Result of infer for " ^ print_exp e ^ " was " ^ print_exp res) ;
  res

and infer_universe = function
  | Star -> Set 0
  | Set n -> Set (n + 1)

and check_type (sign, cG : signature * ctx) cP (s : exp) : universe =
  match infer (sign, cG) cP s with
  | Univ u -> u
  | e ->
     Debug.print (fun () -> "Assert universe failed for " ^ print_exp e ^ ".") ;
     raise (Error.Error "Not a universe.")

and check (sign , cG : signature * ctx) cP (e : exp) (t : exp) : unit =
  Debug.print (fun () ->
      "Check called with: " ^ print_exp e ^ ":" ^ print_exp t ^ " in context: " ^ print_ctx cG);
  Debug.indent();
  begin match e, Whnf.whnf sign t with
  (* checkable terms *)
  | Hole _, _ -> () (* holes are always of the right type *)
  | Fn (fs, e), Pi(tel, t) ->
     let sigma = List.map2 (fun f (_, n, _) -> n, Var f) fs tel in
     let t' = subst_list sigma t in
     let cG' = subst_list_on_ctx sigma cG in
     let cGext = List.map2 (fun f (_, _, s) -> f, s) fs (subst_list_on_tel sigma tel) in
     Debug.indent();
     Debug.print (fun () -> "Checking function: " ^ print_exp (Fn (fs, e)) ^ "\nin context " ^ print_ctx cG ^ ".");
     Debug.print (fun () -> "Resulted in ctx " ^ print_ctx cG'
                            ^ "\nwith extension " ^ print_ctx cGext
                            ^ "\nwith renaming " ^ print_subst sigma ^ ".");
     check (sign, cGext @ cG') cP e t' ;
     Debug.deindent()

  | _, Box (g, alpha) when is_syntax e ->
    let cP = contextify sign g in
    check_syn (sign, cG) cP e alpha

  | _ ->
     let t' =
       try infer (sign, cG) cP e
       with Error.Error msg ->
         Debug.print_string msg;
         raise (Error.Error ("Cannot check expression " ^ print_exp e ^ "\n" ^ msg))
     in
     try
       let _, sigma = Unify.unify (sign, cG) t t' in
       (* TODO check, that sigma instantiates all the pending variables (No free vars remaining) *)
       Debug.print (fun () -> "Unification for " ^ print_exp t ^ " with " ^
                                print_exp t' ^ " succeeded with substitution "
                                ^ Unify.print_subst sigma ^ ".")
     with
     | Error.Error msg ->
       let string_e = print_exp e in
       let string_t = print_exp t in
       let string_t' = print_exp t' in
       let message = "Expression: " ^ string_e
                     ^ "\nwas inferred type: " ^ string_t'
                     ^ "\nwhich is not equal to: " ^ string_t ^ " that was checked against.\n"
                     ^"Unification failed with " ^ msg
       in
       Debug.print_string message;
       raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))
  end ;
  Debug.deindent();
  Debug.print (fun() -> "Finished check for " ^ print_exp e) ;
  ()

and check_spine (sign, cG) cP sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
     check (sign, cG) cP e s ;
     let tel', t' = subst_pi (x, e) tel t in
     check_spine (sign, cG) cP sp' tel' t'
  | [], [] -> t
  | _, [] ->
    begin
      match Whnf.whnf sign t with
      | Pi (tel', t') -> check_spine (sign, cG) cP sp tel' t'
      | Box (g, SPi (tel', t')) ->
        let cP = contextify sign g in
        check_syn_spine (sign, cG) cP sp tel' t'
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ print_exp t))
    end
  | [], _ -> Pi (tel, t)

and check_pi (sign, cG) cP tel t =
  match tel with
  | [] -> infer (sign, cG) cP t
  | (_, x, s)::tel' ->
     let us = check_type (sign, cG) cP s in
     let ut = check_pi (sign, (x, s)::cG) cP tel' t in
     begin match ut with
     | Univ Star -> Univ Star (* Star is impredicative *)
     | Univ (Set n) -> Univ (max_universe us (Set n))
     | _ -> raise (Error.Error ("Expression " ^ print_exp (Pi(tel,t)) ^ " cannot be checked to be a type."))
     end

and check_syn_type (sign, cG) cP (e : exp) : unit =
  Debug.print (fun () -> "Checking syntactic type " ^ print_exp e);
  Debug.indent ();
  begin
    match Whnf.whnf sign e with
    | SStar -> ()
    | SPi (tel, e') ->
      let rec check_tel_type cP = function
        | [] -> cP
        | (_, x, s) :: tel ->
          check_syn_type (sign, cG) cP s;
          check_tel_type ((x, s) :: cP) tel
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
      
    
and check_syn (sign, cG) cP (e : exp) (t : exp) =
  Debug.print (fun () -> "Checking syntactic expression " ^ print_exp e ^ " against type " ^ print_exp t);
  Debug.indent ();
  begin
    match e, Whnf.whnf sign t with
    | Lam (f, e), SPi (tel, t) ->
      let cP' = List.map2 (fun f (_, _, e) -> f, e) f tel in
      check_syn (sign, cG) (cP' @ cP) e t
    | Clos (e, s), _ ->
      let cP' = contextify sign (infer_syn (sign, cG) cP s) in
      check_syn (sign, cG) cP' e t
    | Snoc (g, _, e), Ctx ->
      check_syn (sign, cG) cP g Ctx;
      let cP' = contextify sign g in
      check_syn_type (sign, cG) (cP' @ cP) e
    | Nil, Ctx -> ()
    | e, t when is_syntax e ->
      Debug.print(fun ()-> "Expression " ^ print_exp e ^ " is syntactic and thus being inferred");
      let t' = infer_syn (sign, cG) cP e in
      let _ = Unify.unify (sign, cG) t t' in
      ()
    | e, t ->
      Debug.print(fun ()-> "Expression " ^ print_exp e ^ " is not syntactic and thus back to check");
      check (sign, cG) cP e (Box (decontextify cP, t))
  end; Debug.deindent ()
    

and infer_syn (sign, cG) cP (e : exp) =
  Debug.print (fun () -> "Inferring type of syntactic expression " ^ print_exp e);
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
    | Const n -> check_box (sign, cG) cP (lookup_sign sign cP n)
    | BVar i ->
      let t = lookup_bound i cP in
      Debug.print (fun () -> "Looking bound variable " ^ string_of_int i ^ " resulted in type " ^ print_exp t
        ^ "\n Context is [" ^ String.concat "; " (List.map (fun (x, t) -> x ^ ": " ^ print_exp t) cP) ^ "].");
      t
    | EmptyS -> Nil
    | Shift n -> decontextify (drop_suffix cP n)
    | Dot (s, e) ->
      let g = infer_syn (sign, cG) cP s in
      let cP' = contextify sign g in
      let t = infer_syn (sign, cG) cP' e in
      Snoc (g, "_", t)
    | Comp (s1, s2) ->
      let g1 = infer_syn (sign, cG) cP s1 in
      let cP' = contextify sign g1 in
      infer_syn (sign, cG) cP' s2
    | ShiftS s ->
      begin match cP with
      | [] -> raise (Error.Error ("Shifting a substitution in an empty context"))
      | (x, t) :: cP' ->
        let g = infer_syn (sign, cG) cP' s in
        Snoc (g, x, t)
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
      | Pi (tel', t') -> check_spine (sign, cG) cP sp tel' t'
      | SPi (tel', t') -> check_syn_spine (sign, cG) cP sp tel' t
      | Box (g, SPi (tel', t')) ->
        let cD, sigma, cP' = unify_ctx (sign, cG) g cP in
        check_syn_spine (sign, cD) cP' sp (subst_list_on_stel sigma tel') (subst_list sigma t')
      | _ -> raise (Error.Error ("Unconsumed application cannot check against type " ^ print_exp t))
    end
  | [], _ -> SPi (tel, t)
    
and check_spi (sign, cG) cP tel t =
  match tel with
  | [] -> infer_syn (sign, cG) cP t
  | (_, x, s)::tel' ->
    check_syn_type (sign, cG) cP s;
    check_spi (sign, cG) ((x, s) :: cP) tel' t
      
let rec check_tel (sign, cG) cP u tel =
  match tel with
  | [] -> u
  | (_, x, s) :: tel' ->
     if u = Star then
       check_tel (sign, (x, s) :: cG) cP u tel'
     else
       let us = check_type (sign, cG) cP s in
       let u' = max_universe us u in
       Debug.print (fun () -> "Checking telescope at variable " ^ print_name x
                           ^ " which has universe " ^ print_universe us
                           ^ " upgrading telescope's universe from "
                           ^ print_universe u ^ " to " ^ print_universe u');
       check_tel (sign, (x, s) :: cG) cP u' tel'

let rec check_stel (sign, cG) cP tel =
  match tel with
  | [] -> ()
  | (_, x, s) :: tel' ->
    check_syn_type (sign, cG) cP s;
    check_stel (sign, cG) ((x, s) :: cP) tel'

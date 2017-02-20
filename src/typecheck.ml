open Syntax.Int
open Signature
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

let assert_universe : exp -> universe =
  function
  | Univ u -> u
  | e ->
     Debug.print (fun () -> "Assert universe failed for " ^ print_exp e ^ ".") ;
     raise (Error.Error "Not a universe.")

let rec infer (sign, cG : signature * ctx) (e : exp) : exp =
  Debug.print (fun () -> "Infer called with: " ^ print_exp e ^ " in context: " ^ print_ctx cG);
  Debug.indent() ;
  let res =
    begin match e with
    | Annot (e, t) ->
       check (sign, cG) e t ; t
    | Const n ->
       lookup_sign n sign
    | Var n ->

       begin
         try List.assoc n cG
         with Not_found ->
           raise (Error.Violation
                    ("Unbound var after preprocessing, this cannot happen. (Var: " ^ print_name n ^ ")"))
       end
    | App (h, sp) ->
       begin match infer (sign, cG) h with
       | Pi (tel, t) ->
          check_spine (sign, cG) sp tel t
       | _ -> raise (Error.Error "The left hand side of the application was not of function type")
       end

    | Univ u -> Univ (infer_universe u)
    | Pi (tel, t) ->
       check_tel (sign, cG) tel t

    | Box (ctx, e) ->
       (* TODO: only if ctx is a context and e is a syntactic type *)
       Univ Star

    | _ ->
       begin
         Debug.print (fun() -> "Was asked to infer the type of " ^ print_exp e
                               ^ "but the type is not inferrable") ;
         raise (Error.Error "Cannot infer the type of this expression")
       end
    end in
  Debug.deindent ();
  Debug.print(fun() -> "Result of infer for " ^ print_exp e ^ " was " ^ print_exp res) ;
  res

and infer_universe = function
  | Star -> Set 0
  | Set n -> Set (n + 1)

and check (sign , cG : signature * ctx) (e : exp) (t : exp) : unit =
  Debug.print (fun () ->
      "Check called with: " ^ print_exp e ^ ":" ^ print_exp t ^ " in context: " ^ print_ctx cG);
  Debug.indent();
  begin match e, Whnf.whnf sign t with
  (* types and checkable terms *)

  (* | Fn (f, e), Pi(None, s, t) -> *)
  (*    check (sign, (f, s)::cG) e t *)
  (* | Fn (f, e), Pi(Some n, s, t) -> *)
  (*    check (sign, (f, s)::cG) e (subst (n, Var f) t) *)
  | Fn (fs, e), Pi(tel, t) ->
     let t' = List.fold_left2 (fun t f (_, n, s) -> subst(n, Var f) t) t fs tel in
     let cGext = List.map2 (fun f (_, _, s) -> f, s) fs tel in
     check (sign, cGext @ cG) e t'


  (* terms from the syntactic framework *)
  | Lam (f, e), _ -> assert false
  | AppL (e1, e2), _ -> assert false
  | BVar i, _ -> assert false
  | Clos (e1, e2), _ -> assert false
  | EmptyS, _ -> assert false
  | Shift n, _ -> assert false
  | Comma (e1, e2), _ -> assert false
  | Subst (e1, e2), _ -> assert false
  | Nil, _ -> assert false
  | Arr (t, e), _ -> assert false

  | _ ->
     let t' =
       try infer (sign, cG) e
       with Error.Error msg ->
         Debug.print_string msg;
         raise (Error.Error "Cannot check expression")
     in
     try
       let sigma = Unify.unify sign t t' in
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

and check_spine (sign, cG) sp tel t =
  match sp, tel with
  | e::sp', (_, x, s)::tel ->
     check (sign, cG) e s ;
     let tel', t' = subst_tel (x, e) tel t in
     check_spine (sign, (x, s)::cG) sp' tel' t'
  | [], [] -> t
  | _ -> raise (Error.Error "Spine and telescope of different lengths while type checking.")

and check_tel (sign, cG) tel t =
  match tel with
  | [] -> infer (sign, cG) t
  | (_, x, s)::tel' ->
     let us = assert_universe (infer (sign, cG) s) in
     let ut = assert_universe (infer (sign, (x, s)::cG) (Pi(tel', t))) in
     begin match ut with
     | Star -> Univ Star (* Star is impredicative *)
     | Set n -> Univ (max_universe us ut)
     end

let tc_constructor (sign : signature) (u : universe) (n , ct : def_name * exp) : unit =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let u' = assert_universe(infer (sign, []) ct) in
  if le_universe u' u then (* MMMM *)
    (* TODO additionally we should check that
       it really is a constructor for the type *)
    ()
  else
    begin
      Debug.print_string ("Constructor " ^ n ^ " is in universe: " ^ print_universe u');
      Debug.print_string ("but is expected " ^ print_universe u);
      raise (Error.Error ("The constructor " ^ n ^" is in the wrong universe."))
    end

let decls_to_constructors = List.map (fun (n, e) -> Constructor (n, e))

let add_params_to_tp ps = function
  | Pi (tel, t) -> Pi (ps @ tel, t)
  | t -> Pi (ps, t)

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, e, ds) ->
     let add_params = function
       | Pi (tel, t) -> Pi (ps @ tel, t)
       | t -> if Util.empty_list ps then t else Pi (ps, t)
     in
     let t = add_params e in
     Debug.print_string ("Typechecking data declaration: " ^ n ^ ":" ^ print_exp t ^ "\n");
     (* TODO Add positivity checking and check that it build a value of the right type *)
     let u = assert_universe (infer (sign, []) t) in
     let sign' = (Constructor(n,t))::sign in
     let _ = List.map (fun (n, ct) -> tc_constructor sign' u (n, add_params ct)) ds in
     (decls_to_constructors ds) @ sign'


  | Syn (n, ps, e, ds) ->
     Debug.print_string ("Typechecking syn declaration: " ^ n);
     assert false
  | DefPM (n, t, ds) ->
     Debug.print_string ("Typechecking pattern matching definition: " ^ n);
     let _u = assert_universe(infer (sign, []) t) in
     List.iter (fun (p, rhs) -> Matching.check_clause n p rhs t) ds;
     sign                       (* TODO add the new equations to the signature *)
  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let _ = assert_universe(infer (sign, []) t) in
     check (sign, []) e t ;
     (Definition (n, t, e))::sign

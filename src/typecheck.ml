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
       | t -> raise (Error.Error ("The left hand side (" ^ print_exp h ^ ") of the application was of type "
                                  ^ print_exp t ^ " which is not of function type"))
       end

    | Univ u -> Univ (infer_universe u)
    | Pi (tel, t) ->
       check_pi (sign, cG) tel t

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

and check_type (sign, cG : signature * ctx) (s : exp) : universe =
  match infer (sign, cG) s with
  | Univ u -> u
  | e ->
     Debug.print (fun () -> "Assert universe failed for " ^ print_exp e ^ ".") ;
     raise (Error.Error "Not a universe.")

and check (sign , cG : signature * ctx) (e : exp) (t : exp) : unit =
  Debug.print (fun () ->
      "Check called with: " ^ print_exp e ^ ":" ^ print_exp t ^ " in context: " ^ print_ctx cG);
  Debug.indent();
  begin match e, Whnf.whnf sign t with
  (* checkable terms *)
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
         raise (Error.Error ("Cannot check expression " ^ print_exp e))
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

and check_pi (sign, cG) tel t =
  match tel with
  | [] -> infer (sign, cG) t
  | (_, x, s)::tel' ->
     let us = check_type (sign, cG) s in
     let ut = check_type (sign, (x, s)::cG) (Pi(tel', t)) in
     begin match ut with
     | Star -> Univ Star (* Star is impredicative *)
     | Set n -> Univ (max_universe us ut)
     end

let rec check_tel (sign, cG) u tel =
  match tel with
  | [] -> u
  | (_, x, s) :: tel' ->
     if u = Star then
       check_tel (sign, (x, s) :: cG) u tel'
     else
       let us = check_type (sign, cG) s in
       let u' = max_universe us u in
       check_tel (sign, (x, s) :: cG) u' tel'

let tc_constructor (sign , cG : signature * ctx) (u : universe) (tel : tel)
                   (n , tel', (n', es) : def_name * tel * dsig) : signature_entry =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let _ = check_tel (sign, cG) u tel' in
  List.iter2 (check (sign, (ctx_from_tel tel') @ cG)) es (List.map (fun (_,_,t) -> t) tel);
  Constructor (n, tel', (n', es))

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, is, u, ds) ->
     Debug.print_string ("Typechecking data declaration: " ^ n ^ "\n");
     let u' = check_tel (sign, []) u ps in
     let cG = ctx_from_tel ps in
     let u'' = check_tel (sign, cG) u' is in
     let sign' = DataDef (n, ps, is, u'') :: sign in
     (List.map (tc_constructor (sign', cG) u'' (ps @ is)) ds) @ sign'
     (* TODO Add positivity checking *)

  | Syn (n, ps, e, ds) ->
     Debug.print_string ("Typechecking syn declaration: " ^ n);
     assert false
  | DefPM (n, tel, t, ds) ->
     Debug.print_string ("Typechecking pattern matching definition: " ^ n);
     let _u = check_type (sign, []) t in
     List.iter (fun (p, rhs) -> Matching.check_clause n p rhs t) ds;
     sign                       (* TODO add the new equations to the signature *)
  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let _ = check_type (sign, []) t in
     check (sign, []) e t ;
     (Definition (n, t, e))::sign

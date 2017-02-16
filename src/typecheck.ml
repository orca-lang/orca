open Syntax.Int

type signature = (def_name * exp) list
let lookup_sign n sign =
  try
    List.assoc n sign
  with Not_found -> raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))

type ctx = (name * exp) list

let max_universe (e1 : exp) (e2 : exp) : exp =
  match e1, e2 with
  | Set n, Set n' -> Set (max n n')
  | Star, u -> u
  | u, Star -> u
  | _,_ -> raise (Error.Violation "max_universe called with something is not a universe")

(* <= for universes *)
let le_universe (e1 : exp) (e2 : exp) : bool =
  match e1, e2 with
  | Set n, Set n' -> n <= n'
  | Star, _ -> true
  | _, Star -> false
  | _,_ -> raise (Error.Violation "le_universe called with something is not a universe")

let assert_universe : exp -> exp =
  function
  | Set n -> Set n
  | Star -> Star
  | _ -> raise (Error.Error "Not a universe.")

let rec infer (sign, cG : signature * ctx) (e : exp) : exp =
  Debug.print (fun () ->
      let string_ctx = ">>>" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) cG)) ^ "<<<" in
      "Infer called with: " ^ print_exp e ^ " in context: " ^ string_ctx );
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
    | App (e1, e2) ->
     begin match infer (sign, cG) e1 with
     | Pi (None, s, t) ->
        check (sign, cG) e2 s ;
        t
     | Pi (Some n, s, t) ->
        check (sign, cG) e2 s ;
        subst (n, e2) t
     | _ -> raise (Error.Error "The left hand side of the application was not of function type")
     end

  | Star -> Set 0
  | Set n -> Set (n + 1)
  | Pi (Some x, s, t) ->
     let ts = assert_universe (infer (sign, cG) s) in
     let tt = assert_universe (infer (sign, (x , s) :: cG) t) in
     begin match tt with
     | Star -> Star             (* Star is impredicative. *)
     | Set n -> max_universe ts tt
     | _ -> raise (Error.Violation "Impossible case, we asserted universe!")
     end


  | Pi (None, s, t) ->
     let ts = assert_universe (infer (sign, cG) s) in
     let tt = assert_universe (infer (sign, cG) t) in
     begin match tt with
     | Star -> Star             (* Star is impredicative. *)
     | Set n -> max_universe ts tt
     | _ -> raise (Error.Violation "Impossible case, we asserted universe!")
     end

  (* | Pi (None, s, t), u -> *)
  (*    let n' = infer_universe (sign, cG) s in *)
  (*    if le_universe n' u *)
  (*    then check (sign, cG) t u *)
  (*    else raise (Error.Error "Size problem in a function type.") *)

  | Box (ctx, e) ->
     (* TODO: only if ctx is a context and e is a syntactic type *)
     Star

  | _ ->
     begin
       Debug.print (fun() -> "Was asked to infer the type of " ^ print_exp e ^ "but the type is not inferrable") ;
       raise (Error.Error "Cannot infer the type of this expression")
     end
    end in
  Debug.print(fun() -> "Result of infer for " ^ print_exp e ^ " was " ^ print_exp res) ;
  res

and check (sign , cG : signature * ctx) (e : exp) (t : exp) : unit =
  Debug.print (fun () ->
      let string_ctx = ">>>" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) cG)) ^ "<<<" in
      "Check called with: " ^ print_exp e ^ ":" ^ print_exp t ^ " in context: " ^ string_ctx );
  begin match e, Whnf.whnf t with
  (* types and checkable terms *)

  | Fn (f, e), Pi(None, s, t) ->
     check (sign, (f, s)::cG) e t
  | Fn (f, e), Pi(Some n, s, t) ->
     check (sign, (f, s)::cG) e (subst (n, Var f) t)

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
       let sigma = Unify.unify t t' in
       Debug.print (fun () -> "Unification for " ^ print_exp t ^ " with " ^ print_exp t' ^ " succeeded with substitution "
                            ^ Unify.print_subst sigma ^ ".")
     with
     | Error.Error msg ->
       let string_e = print_exp e in
       let string_t = print_exp t in
       let string_t' = print_exp t' in
       let message = "Expression: " ^ string_e
                     ^ "\nwas inferred type: " ^ string_t'
                     ^ "\nwhich is not equal to: " ^ string_t ^ " that was checked against.\n\nUnification failed with " ^ msg
       in
       Debug.print_string message;
       raise (Error.Error ("Term's inferred type is not equal to checked type.\n" ^ message))
  end ;
  Debug.print (fun() -> "Finished check for " ^ print_exp e) ;
  ()

let tc_constructor (sign : signature) (universe : exp) (n , ct : def_name * exp) : unit =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let u' = assert_universe(infer (sign, []) ct) in
  if le_universe u' universe then (* MMMM *)
    (* TODO additionally we should check that
       it really is a constructor for the type *)
    ()
  else
    begin
      Debug.print_string ("Constructor " ^ n ^ " is in universe: " ^ print_exp u');
      Debug.print_string ("but is expected " ^ print_exp universe);
      raise (Error.Error ("The constructor " ^ n ^" is in the wrong universe."))
    end

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, e, ds) ->
     let add_params e = List.fold_left (fun t2 (_, n, t1) -> Pi(Some n, t1, t2)) e ps in
     let t = add_params e in
     Debug.print_string ("Typechecking data declaration: " ^ n ^ ":" ^ print_exp t ^ "\n");
     let u = assert_universe (infer (sign, []) t) in
     let sign' = (n,t)::sign in
     let _ = List.map (fun (n, ct) -> tc_constructor sign' u (n, add_params ct)) ds in
     ds @ sign'

  | Syn (n, ps, e, ds) ->
     Debug.print_string ("Typechecking syn declaration: " ^ n);
     assert false
  | DefPM (n, e, ds) ->
     Debug.print_string ("Typechecking pattern matching definition: " ^ n);
     assert false
  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let _ = assert_universe(infer (sign, []) t) in
     check (sign, []) e t ;
     (n, t)::sign

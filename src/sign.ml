open Syntax
open Syntax.Int
open Print.Int
open Name
open MetaSub
open MetaOp

(* abstracts the stel to produce a telescope where each meta-variable
   corresponds to each variable in stel, a substitution to perform
   the abstraction, and the shorter cP *)
let abstract sign (cP : bctx) (tel : stel) : tel * syn_exp * bctx =
  Debug.print (fun () -> "Abstracting " ^ print_stel tel);
  let extract_sigma sl = List.fold_right (fun (_, _, x) sigma -> Dot(sigma, x)) sl (Shift (List.length sl)) in
  let extend_cP sl = List.fold_right (fun (x, s, _) cP' -> Snoc(cP', x, s)) sl cP in
  let rec abstract tel sl =
    match tel with
    | [] -> [], sl
    | (i, x, s)::tel' ->
       let cP' = extend_cP sl in
       let sigma = extract_sigma sl in
       let xn = Name.gen_name x in
       let sl' = (x, s, Unbox(Var xn, Shift 0)) :: sl in
       let tel'', sl'' = abstract tel' sl'  in
       (i, xn, Box(cP, Whnf.rewrite sign cP (apply_syn_subst sigma s)))::tel'', sl''
  in
  let tel', sl = abstract tel [] in
  Debug.print (fun () -> "Abstracted version is " ^ print_tel (List.map (fun (i, x, t) -> (i, x, Whnf.normalize sign t)) tel'));
  tel', extract_sigma sl, extend_cP sl

let lookup_syn_cons_entry (sign : signature) (c : def_name) (cP : bctx) : tel * spec_dsig =
  match lookup_sign_entry sign c with
  | SConstructor (_, tel, (n, es)) ->
     let tel', sigma, cP' = abstract sign cP tel in
    tel', (n, List.map (fun e -> apply_syn_subst sigma e) es)
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a syntactic constructor."))

let lookup_sign sign n =
  match lookup_sign_entry sign n with
  | Definition (_, [], t, _, _) -> t
  | Definition (_, tel, t, _, _) -> Pi(tel, t)

  | DataDef (_, ps, is, u)
  | CodataDef (_, ps, is, u) ->
     let tel = ps @ is in
     if tel = []
     then Set u
     else Pi (tel, Set u)

  | Constructor (_, is, (n', pes)) ->
     let t =
       if pes = [] then
         Const n'
       else
         App (Const n', pes)
     in
     let t' =
       if is = [] then t else Pi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_exp t');
     t'

  | Observation (_, is, (m, n', es), e) ->
    let t =
      if es = [] then
        Const n'
      else
        App (Const n', es)
    in
    Pi (is @ [Explicit, m, t], e)

  | Program (_,tel,t, _, _) -> if tel = [] then t else Pi (tel, t)
  | PSplit (_, t, _) -> t

  | _ -> raise (Error.Error ("Name " ^ n ^ " is syntactic"))

let lookup_syn_sign sign n =
  match lookup_sign_entry sign n with
  | SpecDef (_, tel) ->
     if tel = []
     then Star
     else (SPi (tel, Star))
  | SConstructor (_, is, (n', pes)) ->
     let t =
       if pes = [] then
         SConst n'
       else
         AppL (SConst n', pes)
     in
     let t' =
       if is = [] then t else SPi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_syn_exp t');
     t'
  | _ -> raise (Error.Error ("Name " ^ n ^ " is not syntactic")) 

(* returns all the constructors of type n *)
let rec lookup_constructors sign n =
  match sign with
    | Constructor(c, tel, (n',ts)) :: sign' when n = n' -> (c, tel, ts) :: lookup_constructors sign' n
    | _ :: sign' -> lookup_constructors sign' n
    | [] -> []

let rec lookup_syn_constructors sign cP n =
  match sign with
  | SConstructor(c, tel, (n',ts)) :: sign' when n = n' ->
    let tel', sigma, cP' = abstract sign cP tel in
    (c, tel', List.map (fun e -> apply_syn_subst sigma e) ts) :: lookup_syn_constructors sign' cP n
    | _ :: sign' -> lookup_syn_constructors sign' cP n
    | [] -> []

let rec print_signature sign = "[" ^ String.concat "; " (List.map signature_entry_name sign) ^ "]"

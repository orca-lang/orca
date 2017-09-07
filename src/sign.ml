open Syntax
open Syntax.Int
open Print.Int
open Name
open MetaSub

type reducible
  = Reduces
  | Stuck

type signature_entry
  = Definition of def_name * tel * exp * exp * reducible (* the name, the type, and the definition *)
  (* name, parameters, constructed type *)
  | Constructor of def_name * tel * dsig
  (* name, indices, type of codata type being eliminated, resulting type *)
  | Observation of def_name * tel * codsig * exp
  | SConstructor of def_name * stel * spec_dsig
  (* name, parameters, indices, resulting universe *)
  | DataDef of def_name * tel * tel * universe
  | CodataDef of def_name * tel * tel * universe
  | SpecDef of def_name * stel
  | Program of def_name * tel * exp * pat_decls * reducible
  | PSplit of def_name * exp * split_tree option

type signature = signature_entry list

let signature_entry_name = function
    | Definition (n', _, _, _, _)
    | Program (n', _, _, _, _)
    | PSplit (n', _, _)
    | DataDef (n', _, _, _)
    | CodataDef (n', _, _, _)
    | SpecDef (n', _)
    | SConstructor (n', _, _)
    | Observation (n', _, _, _)
    | Constructor (n', _, _) -> n'


let rec lookup_sign_entry (sign : signature) (n : def_name) : signature_entry =
  let el en = signature_entry_name en = n
  in
    try
      List.find el sign
    with Not_found ->
      raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))


let is_syn_con (sign : signature) (n : def_name) =
  match lookup_sign_entry sign n with
  | SConstructor _ -> true
  | _ -> false

let lookup_params (sign : signature) (n : def_name) : tel =
  match lookup_sign_entry sign n with
  | DataDef (_, tel, _, _)
  | CodataDef (_, tel, _, _) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " needs to be (co)data type declaration"))

let lookup_syn_def (sign : signature) (n : def_name) : stel =
  match lookup_sign_entry sign n with
  | SpecDef (_, tel) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " not a syntactic type"))

let lookup_cons_entry (sign : signature) (c : def_name) : tel * dsig =
  match lookup_sign_entry sign c with
  | Constructor (_, tel, dsig) -> tel, dsig
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a constructor."))



(* abstracts the stel to produce a telescope where each meta-variable
   corresponds to each variable in stel, a substitution to perform
   the abstraction, and the shorter cP *)
let abstract (cP : bctx) (tel : stel) : tel * syn_exp * bctx =
  let extract_sigma sl = List.fold_right (fun (_, _, x) sigma -> Dot(sigma, x)) sl (Shift (List.length sl)) in
  let extend_cP sl = List.fold_right (fun (x, s, _) cP' -> Snoc(cP', x, s)) sl cP in
  let rec abstract tel sl =
    match tel with
    | [] -> [], sl
    | (i, x, s)::tel' ->
       let cP' = extend_cP sl in
       let sigma = extract_sigma sl in
       let xn = Name.gen_name x in
       let sl' = (x, s, Unbox(Var xn, Shift 0, cP')) :: sl in
       let tel'', sl'' = abstract tel' sl'  in
       (i, xn, Box(cP, Clos (s, sigma, cP')))::tel'', sl''
  in
  let tel', sl = abstract tel [] in
  tel', extract_sigma sl, extend_cP sl

let lookup_syn_cons_entry (sign : signature) (c : def_name) (cP : bctx) : tel * spec_dsig =
  match lookup_sign_entry sign c with
  | SConstructor (_, tel, (n, es)) ->
     let tel', sigma, cP' = abstract cP tel in
    tel', (n, List.map (fun e -> Clos(e, sigma, cP')) es)
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

type lookup_result
  = D of exp                    (* A definition without pattern matching *)
  | P of pat_decls              (* A definition with pattern matching *)
  | N                           (* A non-reducible constant *)
  | S of split_tree             (* A definition with pattern matching (using split tree) *)

let lookup_sign_def sign n =
  match lookup_sign_entry sign n with
  | Definition (_, _, _, _, Stuck) -> N (* if it is stuck it does not reduce *)
  | Definition (_, _, _, e, _) -> D e
  | Constructor _ -> N
  | DataDef _ -> N
  | CodataDef _ -> N
  | SConstructor _ -> N
  | SpecDef _ -> N
  | Program (_, _, _, _, Stuck) -> N (* if it is stuck it does not reduce *)
  | Program (_, _, _, ds, _) -> P ds
  | PSplit (_, _, None) -> N (* if it is stuck it does not reduce *)
  | PSplit (_, _, Some split) -> S split
  | Observation _ -> raise (Error.Violation "Observation not implemented")

(* returns all the constructors of type n *)
let rec lookup_constructors sign n =
  match sign with
    | Constructor(c, tel, (n',ts)) :: sign' when n = n' -> (c, tel, ts) :: lookup_constructors sign' n
    | _ :: sign' -> lookup_constructors sign' n
    | [] -> []

let rec lookup_syn_constructors sign cP n =
  match sign with
  | SConstructor(c, tel, (n',ts)) :: sign' when n = n' ->
    let tel', sigma, cP' = abstract cP tel in
    (c, tel', List.map (fun e -> Clos(e, sigma, cP')) ts) :: lookup_syn_constructors sign' cP n
    | _ :: sign' -> lookup_syn_constructors sign' cP n
    | [] -> []

let rec print_signature sign = "[" ^ String.concat "; " (List.map signature_entry_name sign) ^ "]"

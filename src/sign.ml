open Syntax
open Syntax.Int
open Print.Int
open Name
open MetaSub

type signature_entry
  = Definition of def_name * tel * exp * exp (* the name, the type, and the definition *)
  (* name, parameters, constructed type *)
  | Constructor of def_name * tel * dsig
  | SConstructor of def_name * stel * dsig
  (* name, parameters, indices, resulting universe *)
  | DataDef of def_name * tel * tel * universe
  | SynDef of def_name * stel
  | Program of def_name * tel * exp * pat_decls

type signature = signature_entry list

let signature_entry_name = function
    | Definition (n', _, _, _)
    | Program (n', _, _, _)
    | DataDef (n', _, _, _)
    | SynDef (n', _)
    | SConstructor (n', _, _)
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

let lookup_syn_def (sign : signature) (n : def_name) : stel =
  match lookup_sign_entry sign n with
  | SynDef (_, tel) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " not a syntactic type"))

let lookup_cons_entry (sign : signature) (c : def_name) : tel * dsig =
  match lookup_sign_entry sign c with
  | Constructor (_, tel, dsig) -> tel, dsig
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a constructor."))

let lookup_syn_cons_entry (sign : signature) (c : def_name) (cP : bctx) : tel * dsig =
  match lookup_sign_entry sign c with
  | SConstructor (_, tel, (n, es)) ->
    let extract_sigma sl = List.fold_right (fun (_, _, x) sigma -> Dot(sigma, x)) sl (Shift (List.length sl)) in
    let extend_cP sl = List.fold_right (fun (x, s, _) cP -> Snoc(cP, x, s)) sl cP in
    let rec abstract tel sl =
      match tel with
      | [] -> [], sl
      | (i, x, s)::tel' ->
         let cP' = extend_cP sl in
         let sigma = extract_sigma sl in
         let xn = Name.gen_name x in
         let sl' = (x, s, Var xn) :: sl in
         let tel'', sl'' = abstract tel' sl'  in
         (i, xn, Box(cP, Clos (s, sigma, cP')))::tel'', sl''
    in
    let tel', sl = abstract tel [] in
    let sigma = extract_sigma sl in
    let cP' = extend_cP sl in
    tel', (n, List.map (fun e -> Clos (e, sigma, cP')) es)
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a syntactic constructor."))

let lookup_sign sign n =
  match lookup_sign_entry sign n with
  | Definition (_, [], t, _) -> t
  | Definition (_, tel, t, _) -> Pi(tel, t)

  | DataDef (_, ps, is, u) ->
     let tel = ps @ is in
     if tel = []
     then Set u
     else Pi (tel, Set u)
  | SynDef (_, tel) ->
     if tel = []
     then Star
     else (SPi (tel, Star))
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
  | SConstructor (_, is, (n', pes)) ->
     let t =
       if pes = [] then
         Const n'
       else
         AppL (Const n', pes)
     in
     let t' =
       if is = [] then t else SPi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_exp t');
     t'

  | Program (_,tel,t, _) -> if tel = [] then t else Pi (tel, t)

type lookup_result
  = D of exp                    (* A definition without pattern matching *)
  | P of pat_decls              (* A definition with pattern matching *)
  | N                           (* A non-reducible constant *)

let lookup_sign_def sign n =
  match lookup_sign_entry sign n with
  | Definition (_, _, _, e) -> D e
  | Constructor _ -> N
  | DataDef _ -> N
  | SConstructor _ -> N
  | SynDef _ -> N
  | Program (_, _, _, ds) -> P ds

(* returns all the constructors of type n *)
let lookup_constructors sign n =
  let constructs_n = function
    | Constructor(_, _, (n',_)) -> n = n'
    | _ -> false
  in
  List.map signature_entry_name (List.filter constructs_n sign)

let rec print_signature sign = "[" ^ String.concat "; " (List.map signature_entry_name sign) ^ "]"

type ctx = (name * exp) list

let print_ctx c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) c)) ^ "]"

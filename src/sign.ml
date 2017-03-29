open Syntax
open Syntax.Int
open Print.Int
open Name

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

let lookup_syn_cons_entry (sign : signature) (c : def_name) (g : exp) : tel * dsig =
  match lookup_sign_entry sign c with
  | SConstructor (_, tel, (n, es)) ->
    let rec abstract tel sl =
      match tel with
      | [] -> [], sl
      | (i, x, s)::tel' ->
         let sigma = List.fold_right (fun x sigma -> Dot(sigma, x)) sl (Shift (List.length sl)) in
         let xn = Name.gen_name x in
         let sl' = Var xn :: sl in
         let tel'', sl'' = abstract tel' sl'  in
         (i, xn, Box(g, Clos (s, sigma)))::tel'', sl''
    in
    let tel', sl = abstract tel [] in
    let sigma = List.fold_right (fun x sigma -> Dot(sigma, x)) sl (Shift (List.length sl)) in
    tel', (n, List.map (fun e -> Clos (e, sigma)) es)
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

type bctx =
| BNil
| CtxVar of name
| BSnoc of bctx * string * exp

let rec append_bctx cP cP' =
  match cP with
  | BNil -> cP'
  | CtxVar _ -> raise (Error.Violation "Appended a bctx terminating with a CtxVar to another bctx")
  | BSnoc (cP, x, e) -> BSnoc (append_bctx cP cP', x, e)

let lookup_bound_name cP x =
  let rec lookup cP i =
    match cP with
    | BSnoc (_, x', t) when x = x' -> i, Clos(t, Shift (i+1))
    | BSnoc (cP', _, _) -> lookup cP' (i+1)
    | _ -> raise (Error.Error ("Bound variable " ^ x ^ " not found in bound context"))
  in
  lookup cP 0

let lookup_bound cP x =
  let rec lookup cP i =
    match cP with
    | BSnoc (_, _, t) when i = 0 -> Clos(t, Shift (x+1))
    | BSnoc (cP', _, _) -> lookup cP' (i-1)
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup cP x

let rec bctx_of_lam_stel (fs : string list) (tel : stel) (cP : bctx) : bctx * stel=
    match fs, tel with
    | [], tel' -> cP, tel'
    | f::fs', (_, _, t)::tel' ->
       let cP, tel'' = bctx_of_lam_stel fs' tel' cP in
       BSnoc (cP , f, t), tel''
    | _, [] -> raise (Error.Error ("Too many variables declared in lambda"))

let bctx_of_stel cP tel =
  let rec make = function
    | [] -> cP
    | (_, x, s)::tel' -> BSnoc (make tel', x, s)
  in
  make (List.rev tel)

let rec bctx_of_ctx_exp = function
  | Snoc(g, x, e) -> BSnoc(bctx_of_ctx_exp g, x, e)
  | _ -> BNil

let print_bctx cP =
  let rec print = function
    | BNil -> ""
    | CtxVar x -> print_name x
    | BSnoc(BNil, x, t) -> x ^ ":" ^ print_exp t
    | BSnoc(g, x, t) -> print g ^ ", " ^ x ^ ":" ^ print_exp t
  in
  "{" ^ print cP ^ "}"

let drop_suffix cP n =
    let rec drop cP' n' =
      match cP', n' with
      | _, 0 -> cP'
      | BSnoc(cP', _, _), n' -> drop cP' (n'-1)
      | _ -> raise (Error.Error ("Tried to drop " ^ string_of_int n ^ " terms out of " ^ print_bctx cP ^ " which is too short."))
    in
    drop cP n

let rec beautify_bound_name x cP =
  let rec count = function
    | CtxVar _
      | BNil -> 0
    | BSnoc (cP', x', _) when x = x' -> 1 + count cP'
    | BSnoc (cP', x', _) -> count cP'
  in
  let c = count cP in
  if c = 0 then x
  else x ^ string_of_int c

let rec beautify_bound_names xs cP =
  match xs with
  |[] -> []
  | x::xs ->
    let x' = beautify_bound_name x cP in
    x'::beautify_bound_names xs (BSnoc (cP, x, Star)) (* star is a dummy type *)

let rec beautify_idx i cP =
  if not (do_beautify ()) then None
  else match i, cP with
  | _, CtxVar _
  | _, BNil -> None
  | 0, BSnoc(cP', x, _) -> Some (beautify_bound_name x cP')
  | i, BSnoc(cP', _, _) -> beautify_idx (i-1) cP'

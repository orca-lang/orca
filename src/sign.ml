open Syntax.Int
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

let rec lookup_sign_entry (n : def_name) (sign : signature) : signature_entry =
  let el en = signature_entry_name en = n
  in
    try
      List.find el sign
    with Not_found ->
      raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))

let lookup_syn_def (n : def_name) (sign : signature) : stel =
  match lookup_sign_entry n sign with
  | SynDef (_, tel) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " not a syntactic type"))

let lookup_cons_entry (c : def_name) (sign : signature) : tel * dsig =
  match lookup_sign_entry c sign with
  | Constructor (_, tel, dsig) -> tel, dsig
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a constructor."))

let lookup_sign sign n =
  (* We generate a new context variable to allow it to be unified with
     any context from the environment. *)
  let flex_box e = Box (Var (gen_floating_name ()) , e) in
  match lookup_sign_entry n sign with
  | Definition (_, [], t, _) -> t
  | Definition (_, tel, t, _) -> Pi(tel, t)

  | DataDef (_, ps, is, u) ->
     let tel = ps @ is in
     if tel = []
     then Univ u
     else Pi (tel, Univ u)
  | SynDef (_, tel) ->
     if tel = []
     then flex_box SStar
     else flex_box (SPi (tel, SStar))
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
         App (Const n', pes)
     in
     let t' =
       if is = [] then t else SPi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_exp t');
     flex_box t'

  | Program (_,tel,t, _) -> if tel = [] then t else Pi (tel, t)


type lookup_result
  = D of exp                    (* A definition without pattern matching *)
  | P of pat_decls              (* A definition with pattern matching *)
  | N                           (* A non-reducible constant *)

let lookup_sign_def n sign =
  match lookup_sign_entry n sign with
  | Definition (_, _, _, e) -> D e
  | Constructor _ -> N
  | DataDef _ -> N
  | SConstructor _ -> N
  | SynDef _ -> N
  | Program (_, _, _, ds) -> P ds

(* returns all the constructors of type n *)
let lookup_constructors n sign =
  let constructs_n = function
    | Constructor(_, _, (n',_)) -> n = n'
    | _ -> false
  in
  List.map signature_entry_name (List.filter constructs_n sign)

(* Given the name of a type and a spine, return the parameter, the indices *)
let split_idx_param (sign : signature) (n : def_name) (es : exp list) : exp list * exp list =
  match lookup_sign_entry n sign with
  | DataDef (_, ps, is, _) ->
     Debug.print (fun () -> "Splitting parameters " ^ print_exps es ^ " against " ^ print_tel ps);
     let rec split = function
       | e::es, _::ps ->
          let es1, es2 = split (es, ps) in
          e::es1, es2
       | es, [] -> [], es
       | _ -> raise (Error.Violation "Ran out of parameters.")
     in
     split (es, ps)
  | _ -> raise (Error.Error ("split_idx_param expected a datatype."))

let rec print_signature sign = "[" ^ String.concat "; " (List.map signature_entry_name sign) ^ "]"

type ctx = (name * exp) list

let print_ctx c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) c)) ^ "]"

let ctx_of_tel : tel -> ctx = List.map (fun (_, x, s) -> x, s)

let exp_list_of_ctx : ctx -> exp list = List.map snd

let subst_of_ctx : ctx -> subst = List.map (fun (x, _) -> x, Var x)

let psubst_of_ctx : ctx -> psubst = List.map (fun (x, _) -> x, PVar x)

let name_list_of_ctx : ctx -> name list = List.map fst

let var_list_of_ctx : ctx -> exp list = List.map (fun (x, _) -> Var x)

let pvar_list_of_ctx : ctx -> pat list = List.map (fun (x, _) -> PVar x)

let rec ctx_subst s = function
  | (x, t) :: cG -> (x, subst s t) :: (ctx_subst s cG)
  | [] -> []

let shift_subst_by_ctx sigma cG =
  let sigma' = sigma @ (List.map (fun (x, _) -> x, Var x) cG) in
  Debug.print (fun () -> "Shift called with sigma = " ^ print_subst sigma
                         ^ "\ncG = " ^ print_ctx cG
                         ^ "\nresulting in " ^ print_subst sigma'
                         ^ ".");
  sigma'

let shift_psubst_by_ctx sigma cG =
  let sigma' = sigma @ (List.map (fun (x, _) -> x, PVar x) cG) in
  Debug.print (fun () -> "Shift called with sigma = " ^ print_psubst sigma
                         ^ "\ncG = " ^ print_ctx cG
                         ^ "\nresulting in " ^ print_psubst sigma'
                         ^ ".");
  sigma'

let subst_list_on_ctx sigma =
    List.map (fun (x, e) -> x, subst_list sigma e)

let simul_psubst_on_ctx sigma =
    List.map (fun (x, e) -> x, simul_psubst sigma e)

let rec rename_ctx_using_pats (cG : ctx) (ps : pats) =
  match cG, ps with
  | [], [] -> []
  | (x, t) :: cG', PVar y :: ps' -> (y, t) :: (rename_ctx_using_pats cG' ps')
  | s :: cG', _ :: ps' -> s :: (rename_ctx_using_pats cG' ps')
  | _ -> raise (Error.Violation "rename_ctx_using_pats. Both arguments should have same length")

let lookup_ctx cG n =
  try
    Some (List.assoc n cG)
  with
    Not_found -> None

let rec rename_ctx_using_subst (cG : ctx) (sigma : subst) =
  match cG with
  | [] -> []
  | (x, t) :: cG' ->
     match lookup_ctx sigma x with
     | Some (Var y) -> (y, t) :: (rename_ctx_using_subst cG' sigma)
     | _ -> (x, t) :: (rename_ctx_using_subst cG' sigma)

let rec rename_ctx_using_psubst (cG : ctx) (sigma : psubst) =
  match cG with
  | [] -> []
  | (x, t) :: cG' ->
     match lookup_ctx sigma x with
     | Some (PVar y) -> (y, t) :: (rename_ctx_using_psubst cG' sigma)
     | _ -> (x, t) :: (rename_ctx_using_psubst cG' sigma)


type bctx =
| BNil
| CtxVar of name
| BSnoc of bctx * string * exp

let rec append_bctx cP cP' =
  match cP with
  | BNil -> cP'
  | CtxVar _ -> raise (Error.Violation "Appended a bctx terminating with a CtxVar to another bctx")
  | BSnoc (cP, x, e) -> BSnoc (append_bctx cP cP', x, e)

let rec lookup_bound i cP =
  match i, cP with
  | 0, BSnoc (_, _, t) -> t
  | n, BSnoc (cP', _, _) -> lookup_bound (n-1) cP'
  | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))

let rec bctx_of_lam_stel (f : string list) (tel : stel) =
    match f, tel with
    | [], tel' -> BNil, tel'
    | f::fs, (_, _, t)::tel' ->
      let cP, tel'' = bctx_of_lam_stel fs tel' in
      BSnoc (cP, f, t), tel''
    | _, [] -> raise (Error.Error ("Too many variables declared in lambda"))

let bctx_of_stel tel =
  let rec make = function
    | [] -> BNil
    | (_, x, s)::tel' -> BSnoc (make tel', x, s)
  in
  make (List.rev tel)

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
      | _, 0 -> cP
      | BSnoc(cP', _, _), n' -> drop cP' (n'-1)
      | _ -> raise (Error.Error ("Tried to drop " ^ string_of_int n ^ " terms out of " ^ print_bctx cP ^ " which is too short."))
    in
    drop cP n

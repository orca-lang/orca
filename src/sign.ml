open Syntax.Int
open Name

type signature_entry
  = Definition of def_name * exp * exp (* the name, the type, and the definition *)
  (* name, parameters, constructed type *)
  | Constructor of def_name * tel * dsig
  (* name, parameters, indices, resulting universe *)
  | DataDef of def_name * tel * tel * universe
  | Program of def_name * tel * exp (* TODO define this *)

type signature = signature_entry list

let signature_entry_name = function
    | Definition (n', _, _)
    | Program (n', _, _)
    | DataDef (n', _, _, _)
    | Constructor (n', _, _) -> n'

let rec lookup_sign_entry (n : def_name) (sign : signature) : signature_entry =
  let el en = signature_entry_name en = n
  in
    try
      List.find el sign
    with Not_found ->
      raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))

let lookup_cons_entry (c : def_name) (sign : signature) : tel * dsig =
  match lookup_sign_entry c sign with
  | Constructor (_, tel, dsig) -> tel, dsig
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a constructor."))

let lookup_sign n sign =
  match lookup_sign_entry n sign with
  | Definition (_, t, _) -> t
  | DataDef (_, ps, is, u) ->
     let tel = ps @ is in
     if Util.empty_list tel
     then Univ u
     else Pi (tel, Univ u)
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
  | Program (_,tel,t) -> if tel = [] then t else Pi (tel, t)

let lookup_sign_def n sign =
  match lookup_sign_entry n sign with
  | Definition (_, _, e) -> Some e
  | Constructor _ -> None
  | DataDef _ -> None
  | Program _ -> assert false

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
     let rec split = function
       | e::es, _::ps ->
          let es1, es2 = split (es, ps) in
          e::es1, es2
       | es, [] -> [], es
       | _ -> raise (Error.Violation "Run out of parameters.")
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

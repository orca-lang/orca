open Syntax.Int
open Name

type signature_entry
  = Definition of def_name * exp * exp (* the name, the type, and the definition *)
  (* name, parameters, constructed type *)
  | Constructor of def_name * tel * dsig
  (* name, parameters, indices, resulting universe *)
  | DataDef of def_name * tel * tel * universe
  | Program of def_name * tel * exp

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
  | Program (_,_,t) -> t

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

let rec print_signature sign = "[" ^ String.concat "; " (List.map signature_entry_name sign) ^ "]"

type ctx = (name * exp) list

let print_ctx c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) c)) ^ "]"

let ctx_from_tel tel = List.map (fun (_, x, s) -> x, s) tel

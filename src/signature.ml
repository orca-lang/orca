open Syntax.Int

type signature_entry
  = Definition of def_name * exp * exp (* the name, the type, and the definition *)
  | Constructor of def_name * exp

type signature = signature_entry list

let rec lookup_sign_entry (n : def_name) (sign : signature) : signature_entry =
  let el = function
    | Definition (n', _, _)
      | Constructor (n', _) -> n = n'
  in
    try
      List.find el sign
    with Not_found ->
      raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))

let lookup_sign n sign =
  match lookup_sign_entry n sign with
  | Definition (_, t, _) -> t
  | Constructor (_, t) -> t

let lookup_sign_def n sign =
  match lookup_sign_entry n sign with
  | Definition (_, t, e) -> Some (Annot(e, t))
  | Constructor _ -> None

type ctx = (name * exp) list

let print_ctx c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) c)) ^ "]"

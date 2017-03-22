open Syntax
open Syntax.Int
open Print.Int
open Meta
open Name

type signature_entry
  = Definition of def_name * tel * exp * exp (* the name, the type, and the definition *)
  (* name, parameters, constructed type *)
  | Constructor of def_name * tel * dsig
  | SConstructor of def_name * tel * dsig
  (* name, parameters, indices, resulting universe *)
  | DataDef of def_name * tel * tel * universe
  | SynDef of def_name * tel
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

let lookup_syn_def (n : def_name) (sign : signature) : tel =
  match lookup_sign_entry n sign with
  | SynDef (_, tel) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " not a syntactic type"))

let lookup_cons_entry (c : def_name) (sign : signature) (mg : exp option) : tel * dsig =
  match lookup_sign_entry c sign, mg with
  | Constructor (_, tel, dsig), None -> tel, dsig
  | SConstructor (_, tel, dsig), Some g ->
    let rec box n = function
      | Var x when n = 0 -> Var x
      | Var x -> Clos (Var x, Shift n)
      | SPi(tel, t) ->
        let tel', t' = box_spi n tel t in
        SPi(tel', t')
      | Pi(tel, t) ->
        Pi (List.map (fun (i, x, s) -> i, x,  box n s) tel, box n t)
      | Const x -> Const x
      | Fn (xs, e) -> Fn (xs, box n e)
      | App (e, es) -> App (box n e, List.map (box n) es)
      | AppL (e, es) -> AppL (box n e, List.map (box n) es)
      | Lam (xs, e) -> Lam (xs, box (n+(List.length xs)) e)
      | BVar i -> BVar i
      | Hole x -> Hole x
      | Annot (e1, e2) -> Annot (box n e1, box n e2)
      | _ -> raise (Error.Violation ("Found reference to substitution or context in definition of syntactic constructor "
                                     ^ c))
    and box_spi n tel t = match tel with
      | [] -> [], box n t
      | (i, x, s) :: tel ->
        let tel', t' = box_spi (n+1) tel t in
        (i, x, box n s) :: tel', t'
    in
    List.map (fun (i, x, s) -> i, x, Box (g, box 0 s)) tel, dsig
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a constructor."))

let lookup_sign sign n =
  (* (\* We generate a new context variable to allow it to be unified with *)
  (*    any context from the environment. *\) *)
  (* let flex_box e = Box (Var (gen_floating_name ()) , e) in *)
  match lookup_sign_entry n sign with
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
     else (Pi (tel, Star))
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
       if is = [] then t else Pi (is, t)
     in
     Debug.print (fun () -> "Looked up constructor " ^ n ^ " which has type " ^ print_exp t');
     t'

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
  | SynDef _ ->
    [], es
  | _ -> raise (Error.Error ("split_idx_param expected a datatype."))

let rec print_signature sign = "[" ^ String.concat "; " (List.map signature_entry_name sign) ^ "]"

type ctx = (name * exp) list

let print_ctx c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) c)) ^ "]"

let ctx_of_tel : tel -> ctx = List.map (fun (_, x, s) -> x, s)

let exp_list_of_ctx : ctx -> exp list = List.map snd

let subst_of_ctx : ctx -> subst = List.map (fun (x, _) -> x, Var x)

let name_list_of_ctx : ctx -> name list = List.map fst

let var_list_of_ctx : ctx -> exp list = List.map (fun (x, _) -> Var x)

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

let simul_subst_on_ctx sigma =
    List.map (fun (x, e) -> x, simul_subst sigma e)

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

type bctx =
| BNil
| CtxVar of name
| BSnoc of bctx * string * exp

let rec append_bctx cP cP' =
  match cP with
  | BNil -> cP'
  | CtxVar _ -> raise (Error.Violation "Appended a bctx terminating with a CtxVar to another bctx")
  | BSnoc (cP, x, e) -> BSnoc (append_bctx cP cP', x, e)

let lookup_bound_name x cP =
  let rec lookup i cP =
    match cP with
    | BSnoc (_, x', t) when x = x' -> i, Clos(t, Shift (i+1))
    | BSnoc (cP', _, _) -> lookup (i+1) cP'
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup 0 cP

let lookup_bound x cP =
  let rec lookup i cP =
    match cP with
    | BSnoc (_, _, t) when i = 0 -> Clos(t, Shift (x+1))
    | BSnoc (cP', _, _) -> lookup (i-1) cP'
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup x cP

let rec bctx_of_lam_stel (fs : string list) (tel : stel) (cP : bctx) : bctx * stel=
    match fs, tel with
    | [], tel' -> cP, tel'
    | f::fs', (_, _, t)::tel' ->
       let cP, tel'' = bctx_of_lam_stel fs' tel' cP in
       BSnoc (cP , f, t), tel''
    | _, [] -> raise (Error.Error ("Too many variables declared in lambda"))

let bctx_of_stel tel =
  let rec make = function
    | [] -> BNil
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

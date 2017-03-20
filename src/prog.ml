open Sign
open Syntax
open Syntax.Apx
open Print.Apx
open Meta
open Match
open Recon

module I = Syntax.Int
module IP = Print.Int

let tc_constructor (sign , cG : signature * ctx) (u : I.universe) (tel : I.tel)
                   (n , tel', (n', es) : def_name * tel * dsig) : signature_entry * I.decl =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let tel'', uc = check_tel (sign, cG) u tel' in
  if uc <= u then
    begin
      let check' = check (sign, (ctx_of_tel tel'') @ cG) in
      let rec check_indices es tel =
        match es, tel with
        | [], [] -> []
        | e::es', (_, x, t)::tel' ->
           let e' = check' e t in
           e'::check_indices es' (simul_subst_on_tel [x, e'] tel')
        | _ -> raise (Error.Error ("Constructor " ^ n
             ^ " does not return a term of the fully applied type for " ^ n'))
      in
      Debug.print (fun () -> "Checking indices applied to " ^ n' ^ " at the tail of signature of " ^ n
        ^ "\nes = (" ^ String.concat ", " (List.map print_exp es) ^ ")\ntel = " ^ IP.print_tel tel);
      let es' = check_indices es tel in
      Constructor (n, tel'', (n', es')), (n, tel'', (n', es'))
    end
  else
    raise (Error.Error ("Constructor " ^ n ^ " has universe " ^ print_universe uc
                        ^ " which does not fit in " ^ print_universe u
                        ^ ", the universe of the data type " ^ n'))

let rec tc_constructors (sign , cG : signature * ctx) (u : I.universe) (tel : I.tel)
                    (ds : decls) : signature * I.decls =
  match ds with
  | [] -> sign, []
  | d::ds ->
     let se, d' = tc_constructor (sign, cG) u tel d in
     let sign', ds' = tc_constructors (sign, cG) u tel ds in
     se::sign', d'::ds'

let tc_syn_constructor (sign , cG : signature * ctx) (tel : I.tel)
                       (n , tel', (n', es) : def_name * tel * dsig) : signature_entry * I.decl =
  Debug.print_string ("Typechecking syntax constructor: " ^ n) ;
  let tel'' = check_syn_tel (sign, cG) tel' in
  (* let cP = bctx_of_stel tel' in *)
  let check' = check_syn (sign, (ctx_of_tel tel'') @ cG) BNil in
  let rec check_indices es tel =
    match es, tel with
    | [], [] -> []
    | e::es', (_, _, t)::tel' ->
       let e' = check' e t in
       e' :: check_indices es' (List.map (fun (i, x, t) -> i, x, (I.Clos(t, I.Dot (I.Shift 1, e')))) tel'')
    | _ -> raise (Error.Error ("Constructor " ^ n
             ^ " does not return a term of the fully applied type for " ^ n'))
  in
  Debug.print (fun () -> "Checking indices applied to " ^ n' ^ " at the tail of signature of " ^ n);
  let es' = check_indices es tel in
  SConstructor (n, tel'', (n', es')), (n, tel'', (n', es'))

let rec tc_syn_constructors (sign , cG : signature * ctx) (tel : I.tel)
                        (ds : decls) : signature * I.decls =
  match ds with
  | [] -> sign, []
  | d::ds ->
     let se, d' = tc_syn_constructor (sign, cG) tel d in
     let sign', ds' = tc_syn_constructors (sign, cG) tel ds in
     se::sign', d'::ds'

let tc_program (sign : signature) : program -> signature * I.program = function
  | Data (n, ps, is, u, ds) ->
    Debug.print_string ("Typechecking data declaration: " ^ n ^ "\nps = "
                        ^ print_tel ps ^ "\nis = " ^ print_tel is);
     let ps', u' = check_tel (sign, []) u ps in
     let cG = ctx_of_tel ps' in
     let is', u'' = check_tel (sign, cG) u' is in
     let sign' = DataDef (n, ps', is', u'') :: sign in
     let sign'', ds' = tc_constructors (sign', cG) u (ps' @ is') ds in
     sign'', I.Data(n, ps', is', u'', ds')
     (* TODO Add positivity checking *)

  | Codata (n, ps, is, u, ds) -> assert false

  | Syn (n, tel, ds) ->
    Debug.print_string ("Typechecking syn declaration: " ^ n);
    let tel' = check_syn_tel (sign, []) tel in
    let sign' = SynDef (n, tel') :: sign in
    let sign'', ds' = tc_syn_constructors (sign', []) tel' ds in
    sign'', I.Syn(n, tel', ds')

  | DefPM (n, tel, t, ds) ->
     Debug.print_string ("\nTypechecking pattern matching definition: " ^ n);
     Debug.indent ();
     let t' = if tel = [] then t else Pi(tel, t) in
     let t'', _u = infer_type (sign, []) t' in
     let sign', ds' = match t'' with
       | I.Pi(tel, t) -> check_clauses sign n tel t ds
       | t -> check_clauses sign n [] t ds (* MMMM this might actually be impossible *)
     in
     Debug.deindent ();
     sign', I.DefPM(n, [], t'', ds') (* TODO put the real tel *)

  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let t', _ = infer_type (sign, []) t in
     let tel, t'' = match t' with
       | I.Pi(tel, t') -> tel, t'
       | _ -> [], t'
     in
     let e' = check (sign, []) e t' in
     (Definition (n, tel, t'', e'))::sign, I.Def(n, t', e')

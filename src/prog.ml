open Sign
open Syntax.Apx
open Print.Apx
open Meta
open Match
open Recon

let tc_constructor (sign , cG : signature * ctx) (u : universe) (tel : tel)
                   (n , tel', (n', es) : def_name * tel * dsig) : signature_entry =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let tel'', uc = check_tel (sign, cG) u tel' in
  if uc <= u then
    begin
      let check' = check (sign, (ctx_of_tel tel') @ cG) in
      let rec check_indices es tel =
        match es, tel with
        | [], [] -> ()
        | e::es', (_, x, t)::tel' ->
          check' e t;
          check_indices es' (simul_subst_on_tel [x,e] tel')
        | _ -> raise (Error.Error ("Constructor " ^ n
             ^ " does not return a term of the fully applied type for " ^ n'))
      in
      Debug.print (fun () -> "Checking indices applied to " ^ n' ^ " at the tail of signature of " ^ n
        ^ "\nes = (" ^ String.concat ", " (List.map print_exp es) ^ ")\ntel = " ^ print_tel tel);
      check_indices es tel;
      Constructor (n, tel', (n', es))
    end
  else
    raise (Error.Error ("Constructor " ^ n ^ " has universe " ^ print_universe uc
                        ^ " which does not fit in " ^ print_universe u
                        ^ ", the universe of the data type " ^ n'))

let tc_syn_constructor (sign , cG : signature * ctx) (tel : tel)
                       (n , tel', (n', es) : def_name * tel * dsig) : signature_entry =
  Debug.print_string ("Typechecking syntax constructor: " ^ n) ;
  let tel'' = check_syn_tel (sign, cG) tel' in
  (* let cP = bctx_of_stel tel' in *)
  let check' = check_syn (sign, (ctx_of_tel tel') @ cG) BNil in
  let rec check_indices es tel =
    match es, tel with
    | [], [] -> ()
    | e::es', (_, _, t)::tel' ->
      check' e t;
      check_indices es' (List.map (fun (i, x, t) -> i, x, (Clos(t, Dot (Shift 1, e)))) tel')
    | _ -> raise (Error.Error ("Constructor " ^ n
             ^ " does not return a term of the fully applied type for " ^ n'))
  in
  Debug.print (fun () -> "Checking indices applied to " ^ n' ^ " at the tail of signature of " ^ n);
  check_indices es tel;
  SConstructor (n, tel', (n', es))

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, is, u, ds) ->
    Debug.print_string ("Typechecking data declaration: " ^ n ^ "\nps = "
                        ^ print_tel ps ^ "\nis = " ^ print_tel is);
     let u' = check_tel (sign, []) u ps in
     let cG = ctx_of_tel ps in
     let u'' = check_tel (sign, cG) u' is in
     let sign' = DataDef (n, ps, is, u'') :: sign in
     (List.map (tc_constructor (sign', cG) u (ps @ is)) ds) @ sign'
     (* TODO Add positivity checking *)

  | Codata (n, ps, is, u, ds) -> assert false

  | Syn (n, tel, ds) ->
    Debug.print_string ("Typechecking syn declaration: " ^ n);
    check_syn_tel (sign, []) tel;
    let sign' = SynDef (n, tel) :: sign in
    (List.map (tc_syn_constructor (sign', []) tel) ds) @ sign'


  | DefPM (n, tel, t, ds) ->
     Debug.print_string ("\nTypechecking pattern matching definition: " ^ n);
     Debug.indent ();
     let t' = if tel = [] then t else Pi(tel, t) in
     let _u = check_type (sign, []) t' in
     let sign' = check_clauses sign n tel t ds in
     Debug.deindent ();
     sign'



  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let _ = check_type (sign, []) t in
     let tel, t' = match t with
       | Pi(tel, t') -> tel, t'
       | _ -> [], t
     in
     check (sign, []) e t ;
     (Definition (n, tel, t', e))::sign

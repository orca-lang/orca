open Sign
open Syntax.Int
open Match
open Check

let tc_constructor (sign , cG : signature * ctx) (u : universe) (tel : tel)
                   (n , tel', (n', es) : def_name * tel * dsig) : signature_entry =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let uc = check_tel (sign, cG) BNil u tel' in
  if le_universe uc u then
    begin
      List.iter2 (check (sign, (ctx_of_tel tel') @ cG) BNil) es (List.map (fun (_,_,t) -> t) tel);
      Constructor (n, tel', (n', es))
    end
  else
    raise (Error.Error ("Constructor " ^ n ^ " has universe " ^ print_universe uc
                        ^ " which does not fit in " ^ print_universe u
                        ^ ", the universe of the data type " ^ n'))

let tc_syn_constructor (sign , cG : signature * ctx) (tel : stel)
                       (n , tel', (n', es) : def_name * stel * dsig) : signature_entry =
  Debug.print_string ("Typechecking syntax constructor: " ^ n) ;
  check_stel (sign, cG) BNil tel';
  let cP = bctx_of_stel tel' in
  List.iter2 (check_syn (sign, cG) cP) es (List.map (fun (_,_,t) -> t) tel);
  SConstructor (n, tel', (n', es))

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, is, u, ds) ->
     Debug.print_string ("Typechecking data declaration: " ^ n ^ "\n");
     let u' = check_tel (sign, []) BNil u ps in
     let cG = ctx_of_tel ps in
     let u'' = check_tel (sign, cG) BNil u' is in
     let sign' = DataDef (n, ps, is, u'') :: sign in
     (List.map (tc_constructor (sign', cG) u (ps @ is)) ds) @ sign'
     (* TODO Add positivity checking *)

  | Syn (n, tel, ds) ->
    Debug.print_string ("Typechecking syn declaration: " ^ n);
    let () = check_stel (sign, []) BNil tel in
    let sign' = SynDef (n, tel) :: sign in
    (List.map (tc_syn_constructor (sign', []) tel) ds) @ sign'
    
    
  | DefPM (n, tel, t, ds) ->
     Debug.print_string ("\nTypechecking pattern matching definition: " ^ n);
     Debug.indent ();
     let t' = if tel = [] then t else Pi(tel, t) in
     let _u = check_type (sign, []) BNil t' in
     let sign' = check_clauses sign n tel t ds in
     Debug.deindent ();
     sign'



  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let _ = check_type (sign, []) BNil t in
     let tel, t' = match t with
       | Pi(tel, t') -> tel, t'
       | _ -> [], t
     in
     check (sign, []) BNil e t ;
     (Definition (n, tel, t', e))::sign

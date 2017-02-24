open Sign
open Syntax.Int
open Match
open Check

let tc_constructor (sign , cG : signature * ctx) (u : universe) (tel : tel)
                   (n , tel', (n', es) : def_name * tel * dsig) : signature_entry =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let uc = check_tel (sign, cG) u tel' in
  if le_universe uc u then
    begin
      List.iter2 (check (sign, (ctx_of_tel tel') @ cG)) es (List.map (fun (_,_,t) -> t) tel);
      Constructor (n, tel', (n', es))
    end
  else
    raise (Error.Error ("Constructor " ^ n ^ " has universe " ^ print_universe uc
                        ^ " which does not fit in " ^ print_universe u
                        ^ ", the universe of the data type " ^ n'))

let tc_program (sign : signature) : program -> signature = function
  | Data (n, ps, is, u, ds) ->
     Debug.print_string ("Typechecking data declaration: " ^ n ^ "\n");
     let u' = check_tel (sign, []) u ps in
     let cG = ctx_of_tel ps in
     let u'' = check_tel (sign, cG) u' is in
     let sign' = DataDef (n, ps, is, u'') :: sign in
     (List.map (tc_constructor (sign', cG) u (ps @ is)) ds) @ sign'
     (* TODO Add positivity checking *)

  | Syn (n, ps, e, ds) ->
     Debug.print_string ("Typechecking syn declaration: " ^ n);
     assert false
  | DefPM (n, tel, t, ds) ->
     Debug.print_string ("Typechecking pattern matching definition: " ^ n);
     let u = check_type (sign, []) t in
     let _ = check_tel (sign, []) u tel in
     let sign' = Program(n, tel, t)::sign in
     List.iter (fun (p, rhs) -> check_clause sign' n p tel t rhs) ds;
     sign'                       (* TODO add the new equations to the signature *)
  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     let _ = check_type (sign, []) t in
     check (sign, []) e t ;
     (Definition (n, t, e))::sign

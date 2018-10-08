open Sign
open Syntax
open Syntax.Apx
open Print.Apx
open MetaOp
open MetaSub
open Match
open Recon

module I = Syntax.Int
module IP = Print.Int

type pattern_matching_option
  = Old
  | Split
  | New

let current_pm = ref Split

let parse_pm_option = function
  | "old" -> current_pm := Old
  | "split" -> current_pm := Split
  | "new" -> current_pm := New
  | _ -> raise (Error.Violation "Unknown pattern matching processor specified")

let tc_constructor (sign , cG : I.signature * I.ctx) (u : I.universe) (tel : I.tel)
                   (n , tel', (n', es) : def_name * tel * dsig) : I.signature_entry * I.decl =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let tel'', uc = check_tel (sign, cG) u tel' in
  let cG' = (ctx_of_tel tel'') @ cG in
  if uc <= u then
    begin
      let check' = check (sign, cG') in
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

let rec tc_constructors (sign , cG : I.signature * I.ctx) (u : I.universe) (tel : I.tel)
                    (ds : decls) : I.signature * I.decls =
  match ds with
  | [] -> sign, []
  | d::ds ->
     let se, d' = tc_constructor (sign, cG) u tel d in
     let sign', ds' = tc_constructors (sign, cG) u tel ds in
     se::sign', d'::ds'

let tc_observation (sign , cG : I.signature * I.ctx) (u : I.universe) (tel : I.tel)
                   (n , tel', (m, n', es), e : def_name * tel * codsig * exp) : I.signature_entry * I.codecl =
  Debug.print_string ("Typechecking constructor: " ^ n) ;
  let tel'', uc = check_tel (sign, cG) u tel' in
  let cG' = (ctx_of_tel tel'') @ cG in
  if uc <= u then                       (* Note: Is that check needed for codatatypes? *)
    begin
      let rec check_indices es tel =
        match es, tel with
        | [], [] -> []
        | e::es', (_, x, t)::tel' ->
           let e' = check (sign, cG') e t in
           e'::check_indices es' (simul_subst_on_tel [x, e'] tel')
        | _ -> raise (Error.Error ("Constructor " ^ n
             ^ " does not return a term of the fully applied type for " ^ n'))
      in
      Debug.print (fun () -> "Checking indices applied to " ^ n' ^ " at the tail of signature of " ^ n
        ^ "\nes = (" ^ String.concat ", " (List.map print_exp es) ^ ")\ntel = " ^ IP.print_tel tel);
      let es' = check_indices es tel in
      let e' = check (sign, (m, I.App (I.Const n', es')) :: cG') e (I.Set u) in
      Observation (n, tel'', (m, n', es'), e'), (n, tel'', (m, n', es'), e')
    end
  else
    raise (Error.Error ("Constructor " ^ n ^ " has universe " ^ print_universe uc
                        ^ " which does not fit in " ^ print_universe u
                        ^ ", the universe of the data type " ^ n'))

let rec tc_observations (sign , cG : I.signature * I.ctx) (u : I.universe) (tel : I.tel)
           (ds : codecls) : I.signature * I.codecls =
  match ds with
  | [] -> sign, []
  | d::ds ->
     let se, d' = tc_observation (sign, cG) u tel d in
     let sign', ds' = tc_observations (sign, cG) u tel ds in
     se::sign', d'::ds'

let tc_syn_constructor (sign , cG : I.signature * I.ctx) (tel : I.stel)
                       (n , tel', (n', es) : def_name * stel * dsig) : I.signature_entry * I.sdecl =
  Debug.print_string ("Typechecking syntax constructor: " ^ n) ;
  let tel'' = check_stel (sign, cG) I.Nil tel' in
  let cP = bctx_of_stel I.Nil tel'' in
  let check' = check_syn (sign, cG) cP in
  let rec check_indices es tel cP' s =
    match es, tel with
    | [], [] -> []
    | e::es', (_, x, t)::tel' ->
       let e' = check' e (I.Clos (t, s, cP')) in
       e' :: check_indices es' tel' (I.Snoc(cP', x, t)) (I.Dot(s, e'))
    | _ -> raise (Error.Error ("Constructor " ^ n
             ^ " does not return a term of the fully applied type for " ^ n'))
  in
  Debug.print (fun () -> "Checking indices applied to " ^ n' ^ " at the tail of signature of " ^ n);
  let es' = check_indices es tel cP I.id_sub in
  SConstructor (n, tel'', (n', es')), (n, tel'', (n', es'))

let rec tc_syn_constructors (sign , cG : I.signature * I.ctx) (tel : I.stel)
                        (ds : sdecls) : I.signature * I.sdecls =
  match ds with
  | [] -> sign, []
  | d::ds ->
     let se, d' = tc_syn_constructor (sign, cG) tel d in
     let sign', ds' = tc_syn_constructors (sign, cG) tel ds in
     se::sign', d'::ds'

let tc_program (sign : I.signature) : program -> I.signature * I.program =
  function
  | Data (n, ps, is, u, ds) ->
    Debug.print_string ("Typechecking data declaration: " ^ n ^ "\nps = "
                        ^ print_tel ps ^ "\nis = " ^ print_tel is);
     let ps', u' = check_tel (sign, []) u ps in
     let cG = ctx_of_tel ps' in
     let is', u'' = check_tel (sign, cG) u' is in
     let sign' = I.DataDef (n, ps', is', u'') :: sign in
     let sign'', ds' = tc_constructors (sign', cG) u (ps' @ is') ds in
     sign'', I.Data(n, ps', is', u'', List.rev ds')
     (* TODO Add positivity checking *)

  | Codata (n, ps, is, u, ds) ->
    Debug.print_string ("Typechecking data declaration: " ^ n ^ "\nps = "
                        ^ print_tel ps ^ "\nis = " ^ print_tel is);
    let ps', u' = check_tel (sign, []) u ps in
    let cG = ctx_of_tel ps' in
    let is', u'' = check_tel (sign, cG) u' is in
    let sign' = I.CodataDef (n, ps', is', u'') :: sign in
    let sign'', ds' = tc_observations (sign', cG) u (ps' @ is') ds in
    sign'', I.Codata(n, ps', is', u'', List.rev ds')

  | Spec spec ->
    let spec' = List.map (fun (n, tel, ds) -> n, check_stel (sign, []) I.Nil tel, ds) spec in
    let sign' = List.map (fun (n, tel, ds) -> I.SpecDef (n, tel)) spec' @ sign in
    let rec process sign = function
      | (n, tel, ds) :: spec ->
        Debug.print_string ("Typechecking syn declaration: " ^ n);
        Debug.indent ();
        let sign', ds' = tc_syn_constructors (sign, []) tel ds in
        let sign'', spec' = process sign' spec in
        Debug.deindent ();
        sign'', (n, tel, ds') :: spec'
      | [] -> sign, []
    in
    let sign'', spec'' = process sign' spec' in
    sign'', I.Spec spec''
  | DefPM def ->
    let process_type (n, tel, t, ds) =
      let t' = if tel = [] then t else Pi(tel, t) in
      let t'', _u = infer_type (sign, []) t' in
      let tel', t0 = match t'' with
        | I.Pi(tel, t) -> tel, t
        | t -> [], t
      in
      (n, tel', t0, ds)
    in
    let def' = List.map process_type def in
    let sign_temp = List.map (fun (n, tel, t, ds) -> I.Program (n, tel, t, [], I.Stuck)) def' @ sign in
    begin match !current_pm with
    | Split ->
      let rec process = function
        | (n, tel, t, ds) :: def ->
          Debug.print_string ("\nTypechecking pattern matching definition: " ^ n);
          Debug.indent ();
          let sentry, tree = Split.check_clauses sign_temp n (I.Pi(tel, t)) ds in
          Debug.deindent ();
          let sentries, def' = process def in
          sentry :: sentries, (n, I.Pi(tel, t), tree) :: def'
        | [] -> [], []
      in
      let sentries, def'' = process def' in
      sentries @ sign, I.DefPMTree def''
    | New ->
      let rec process = function
        | (n, tel, t, ds) :: def ->
          Debug.print_string ("\nTypechecking pattern matching definition: " ^ n ^ " using the new split checker");
          Debug.indent ();
          let sentry, tree = Newsplit.check_clauses sign_temp n (I.Pi(tel, t)) ds in
          Debug.deindent ();
          let sentries, def' = process def in
          sentry :: sentries, (n, I.Pi(tel, t), tree) :: def'
        | [] -> [], []
      in
      let sentries, def'' = process def' in
      sentries @ sign, I.DefPMTree def''
    | Old ->
      let rec process = function
        | (n, tel, t, ds) :: def ->
          Debug.print_string ("\nTypechecking pattern matching definition: " ^ n);
          Debug.indent ();
          let sentry, ds' = check_clauses sign_temp n tel t ds in

          Debug.deindent ();
          let sentries, def' = process def in
          sentry :: sentries, (n, tel, t, ds') :: def'
        | [] -> [], []
      in
      let sentries, def'' = process def' in
      sentries @ sign, I.DefPM def''
    end
  | Def (n, t, e) ->
     Debug.print_string ("Typechecking definition: " ^ n);
     Debug.indent ();
     let t', _ = infer_type (sign, []) t in
     let tel, t'' = match t' with
       | I.Pi(tel, t') -> tel, t'
       | _ -> [], t'
     in
     let e' = check (sign, []) e t' in
     Debug.deindent ();
     (Definition (n, tel, t'', e', Reduces))::sign, I.Def(n, Whnf.normalize sign t', Whnf.normalize sign e')

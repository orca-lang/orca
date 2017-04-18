open Syntax
open Print
open Sign
open Recon
open Name
open Procpat

module A = Syntax.Apx
module AP = Print.Apx
module I = Syntax.Int
module IP = Print.Int
open Meta
open MetaSub

type ctx_map = pats

type comp_or_syn
  = Syn of I.syn_exp list
  | Comp of I.exp list

let print_cos = function
  | Syn s -> IP.print_syn_exps s
  | Comp e -> IP.print_exps e

(* Given the name of a type and a spine, return the parameter, the indices *)
let split_idx_param (sign : signature) (cG : ctx) (n : def_name) (es1 : comp_or_syn)
    (es2 : comp_or_syn) : ctx * subst * comp_or_syn * comp_or_syn * comp_or_syn =
  match lookup_sign_entry sign n with
  | DataDef (_, ps, is, _) ->
     (* Debug.print (fun () -> "Splitting parameters " ^ IP.print_exps es1 ^ " against " ^ IP.print_tel ps); *)
     let rec split = function
       | Comp (e::es), _::ps ->
          let es1, es2 = split (Comp es, ps) in
          (e::es1), es2
       | Comp es, [] -> [], es
       | _ -> raise (Error.Violation "Ran out of parameters.")
     in
     let us1, vs1 = split (es1, ps) in
     let us2, vs2 = split (es2, ps) in
     let cD, sigma = Unify.unify_many (sign, cG) us1 us2 in
     cD, sigma, Comp (List.map (simul_subst sigma) us1), Comp (List.map (simul_subst sigma) vs1), Comp (List.map (simul_subst sigma) vs2)
  | SynDef _ ->
    cG, [], Syn [], es1, es2
  | _ -> raise (Error.Error ("split_idx_param expected a datatype."))


let rec rename_ctx_using_pats (cG : ctx) (ps : pats) =
  match cG, ps with
  | [], [] -> [], []
  | (x, t) :: cG', Apx (A.PVar y) :: ps' ->
    let sigma, cD = rename_ctx_using_pats (ctx_subst (x, I.Var y) cG') ps' in
    (x, I.Var y) :: sigma, (y, t) :: cD
  | s :: cG', _ :: ps' ->
    let sigma, cD = rename_ctx_using_pats cG' ps' in
    sigma, s :: cD
  | _ -> raise (Error.Violation "rename_ctx_using_pats. Both arguments should have same length")


let rec subst_of_ctx_map sign (sigma : ctx_map) (tel : I.tel) : subst =
  match sigma, tel with
  | [], [] -> []
  | p :: ps, (_, n, t) :: tel' -> (n, Procpat.exp_of_pat sign I.Nil p) :: (subst_of_ctx_map sign ps tel')
  | _ -> raise (Error.Violation "subst_of_ctx_map got lists of different lengths")

let compose_maps sign (sigma : I.pats) (cD : ctx) (delta : I.pats) : I.pats =
  let delta_names = List.map2 (fun (x, _) p -> x, p) cD delta in
  Debug.print(fun () -> "Composing maps\nsigma = " ^ IP.print_pats sigma
     ^ "\ndelta = " ^ IP.print_pats delta ^ "\ndelta_names" ^ print_psubst delta_names);
  List.map (simul_psubst sign delta_names) sigma

let rec matching (p : I.pat) (q : pat) : pats =
  match p, q with
  | I.PVar n, _ -> [q]
  | I.PPar n, Int(I.PPar n') -> [Int(I.PVar n')]
  | I.PPar n, Apx(A.PPar n') -> [Int(I.PVar n')] (* MMM *)
  | I.PTBox(cP, I.PBVar i), Int(I.PTBox(cP', I.PBVar i')) when cP = cP' && i = i' -> [] (* MMM *)
  | I.PTBox(cP, I.PBVar i), Apx(A.PBVar i') when i = i' -> []
  | I.Innac _, _ -> []
  | I.PConst (n, ps) , Int(I.PConst (n', qs)) when n = n' -> matchings ps (List.map (fun p -> Int p) qs)
  | I.PConst (n, ps) , Apx(A.PConst (n', qs)) when n = n' -> matchings ps (List.map (fun p -> Apx p) qs)

  | I.PConst (n, ps) , Int(I.PConst (n', qs)) -> raise(Error.Error "Pattern matching does not match. (I)")
  | I.PConst (n, ps) , Apx(A.PConst (n', qs)) -> raise(Error.Error "Pattern matching does not match. (A)")
  | I.PTBox (cP, p), Int(I.PTBox(cP', p')) when cP = cP' -> List.map (fun p -> Int(I.PTBox(cP, p))) (syn_matching_int p p')
  | I.PTBox (cP, p), Apx p' -> syn_matching_apx cP p p'

  | _ -> raise (Error.Error ("what is love? p = " ^ IP.print_pat p ^ " q = " ^ print_pat q))

and syn_matching_int (p : I.syn_pat) (q : I.syn_pat) : I.syn_pat list =
  match p, q with
  | I.PLam (xs, p), I.PLam (ys, q) -> syn_matching_int p q
  | I.PUnbox (n, s, cP), I.PUnbox (n', s', cP') when s = s' && cP = cP' -> [I.PUnbox(n', s, cP)] (* big MMMM *)
  | I.PEmpty, I.PEmpty -> []
  | I.PShift n, I.PShift n' when n = n' -> []
  | I.PSConst (n, ps), I.PSConst (n', ps') when n = n' -> List.concat (List.map2 syn_matching_int ps ps')
  | I.PSConst (n, _), I.PSConst (n', _') -> raise (Error.Error (n ^ " is not equal " ^ n'))
  | I.PBVar i, I.PBVar i' when i = i' -> []
  | I.PDot (p1, p2), I.PDot (p1', p2') -> syn_matching_int p1 p1' @ syn_matching_int p2 p2'
  | _ -> raise (Error.Error ("Pats do not match " ^ IP.print_syn_pat p ^ " and " ^ IP.print_syn_pat q))

and syn_matching_int' (p : I.syn_pat) (q : I.pat) : I.syn_pat list =
  match p, q with
  | I.PUnbox (n, CShift 0, cP'), I.PVar n' -> [I.PUnbox(n', CShift 0, cP')]
  | I.PUnbox (n, CShift 0, cP'), I.Innac e -> [I.SInnac(e, CShift 0, cP')]
  | _ -> raise (Error.Error ("bfvPats do not match " ^ IP.print_syn_pat p ^ " and " ^ IP.print_pat q))

and syn_matching_apx cP (p : I.syn_pat) (q : A.pat) : pats =
  match p, q with
  | I.PLam (xs, p), A.PLam (ys, q) -> syn_matching_apx (bctx_from_lam cP xs) p q
  | I.PUnbox (n, s, cP'), A.PClos (n', s') when s = s' -> [Int (I.PTBox (cP, I.PUnbox(n', s, cP')))] (* big MMMM *)
  | I.PUnbox (n, CShift 0, cP'), A.PVar n' -> [Int (I.PTBox (cP, I.PUnbox(n', CShift 0, cP')))]
  | I.PUnbox (n, CShift 0, cP'), A.Innac e -> [Apx (A.SInnac (e, CShift 0))]
  | I.PEmpty, A.PEmptyS -> []
  | I.PShift n, A.PShift n' when n = n' -> []
  | I.PSConst (n, ps), A.PConst (n', ps') when n = n' -> List.concat (List.map2 (syn_matching_apx cP) ps ps')
  | I.PSConst (n, _), A.PConst (n', _') -> raise (Error.Error (n ^ " is not equal " ^ n'))
  | I.PBVar i, A.PBVar i' when i = i' -> []
  | I.PDot (p1, p2), A.PDot (p1', p2') -> syn_matching_apx cP p1 p1' @ syn_matching_apx cP p2 p2'
  | _ -> raise (Error.Error ("Pats do not match " ^ IP.print_syn_pat p ^ " and " ^ AP.print_pat q))

and matchings (sigma : I.pats) (p : pats) : pats =
  match sigma, p with
  | [], [] -> []
  | q::sigma', p :: ps -> (matching q p) @ matchings sigma' ps
  | _ -> raise (Error.Violation ("Matching lists of different size. \nsigma = " ^ IP.print_pats sigma ^ "\np = " ^ print_pats p))

let rec flexible (p : pats)(cG : ctx) : name list =
  match p, cG with
    | [], [] -> []
    | Int (I.Innac _)::ps, (x, t)::cG'
    | Apx (A.Innac _)::ps, (x, t)::cG' -> x::(flexible ps cG')
    | p::ps, (x, t)::cG' -> flexible ps cG'
    | _ -> raise (Error.Violation ("Flexible: length violation."))

let inac_ctx = List.map (fun (_, t) -> I.Innac t)
let inac_subst = List.map (fun (x, e) -> x, I.Innac e)

let split_flex_unify (sign : signature) sigma0 maybe_g (p1 : pats) (thetatel : I.tel) (ps : pats)
                     (cD1 : ctx) (vs : comp_or_syn) (ws : comp_or_syn) =
  let sigma, cT = rename_ctx_using_pats (simul_subst_on_ctx sigma0 (ctx_of_tel thetatel)) ps in
  Debug.print (fun () -> "Creating set of flexible variables\np1 = " ^ print_pats p1
    ^ "\nps = " ^ print_pats ps ^ "\ncD1 = " ^ print_ctx cD1 ^ "\ncT = " ^ print_ctx cT);
  let flex = flexible (p1 @ ps) (cD1 @ cT) in
  Debug.print (fun () -> "Flexibles variables are " ^ print_names flex);
  let f = function
    | Comp vs -> Comp (List.map (simul_subst sigma) vs)
    | Syn vs -> Syn (List.map (simul_subst_syn sigma) vs)
  in
  let vs = f vs in
  let ws = f ws in
  let cD', delta =
    Debug.print (fun () -> "Split unifies\nvs = " ^ print_cos vs ^ "\nws = " ^ print_cos ws);
    try
      match maybe_g, vs, ws with
      | None, Comp vs, Comp ws -> Unify.unify_flex_many (sign, cD1 @ cT) flex vs ws
      | Some cP, Syn vs, Syn ws -> Unify.unify_flex_many_syn (sign, cD1 @ cT) cP flex vs ws
      | _ -> raise (Error.Violation ("Is this a violation or an erro?r"))
    with
      Unify.Unification_failure prob ->
      raise (Error.Error ("Split failed with unification problem " ^ Unify.print_unification_problem prob))
  in
  let delta = delta @ sigma0 in
  Debug.print (fun () -> "Split unification outputed : cD' = " ^ print_ctx cD');
  let cT' = simul_subst_on_ctx delta (rename_ctx_using_subst cT delta) in
  Debug.print (fun () -> "delta = " ^ IP.print_subst delta ^ ", cT = " ^ print_ctx cT ^ ", cT' = " ^ print_ctx cT');
  Debug.print (fun () -> "cD1 = " ^ print_ctx cD1);
  Debug.print (fun () -> "cT = " ^ print_ctx cT ^ "\ncT' = " ^ print_ctx cT');
  let pdelta = inac_subst delta in
  Debug.print (fun () -> "pdelta = " ^ print_psubst pdelta);
  cD', cT, delta, pdelta, cT'

let compute_split_map sign (ss:single_subst) (pss:single_psubst) (cD1:ctx) (x:name)
    (cD2:ctx) (delta : subst) (pdelta : psubst) (cD':ctx) : ctx * I.pats =
  Debug.indent ();
  Debug.print (fun () -> "ss = " ^ IP.print_subst [ss]);
  Debug.print (fun () -> "pss = " ^ print_psubst [pss]);
  Debug.print (fun () -> "cD' = " ^ print_ctx cD');
  let id_cD' = psubst_of_ctx cD1 in
  let delta' = compose_single_with_subst ss (delta @ [x, I.Var x]) in
  Debug.print (fun () -> "delta' = " ^ IP.print_subst delta');
  let pdelta = compose_psubst sign pdelta id_cD' in
  Debug.print (fun () -> "pdelta = " ^ print_psubst pdelta);
  let pdelta_shift = pdelta @ [x, I.PVar x] in
  let pdelta' = compose_single_with_psubst sign pss pdelta_shift in
  Debug.print (fun () -> "pdelta' = " ^ print_psubst pdelta');
  let cD'', delta'' = cD' @ (simul_subst_on_ctx delta' cD2),
    (pats_of_psubst (shift_psubst_by_ctx pdelta' cD2)) in
  (* Debug.print (fun () -> "Split! \ncD2 = " ^ print_ctx cD2 ^ "\ndelta' = " ^ print_psubst pdelta' *)
  (*                        ^ "\n delta'' = " ^ print_pats delta'' ^ "\n cD'' = " ^ print_ctx cD''); *)
  Debug.deindent ();
  cD'', delta''

let rec theta_of_lam cP xs tel =
  match xs, tel with
  | [], _ -> cP, [], tel
  | x::xs, (i,y,t)::tel' ->
     let cP', tel0, tel'' = theta_of_lam cP xs tel' in
     I.Snoc(cP', x, t), (i, y, t)::tel0, tel''
  | _ -> raise (Error.Error ("Something went wrong as always"))

let rec theta_of_lam' g xs tel =
  match xs, tel with
  | [], _ -> g, [], tel
  | x::xs, (i,y,t)::tel' ->
     let g', tel0, tel'' = theta_of_lam' g xs tel' in
     I.Snoc(g', x, t), (i, y, t)::tel0, tel''
  | _ -> raise (Error.Error ("Something went wrong as always"))

let split_lam (sign : signature) (p1 : pats) (xs, p : string list * pat) (cD1 : ctx)
              (x, t : name * I.exp) (cD2 : ctx) : ctx * I.pats =
  Debug.indent ();
  let g, tel, t = match Whnf.whnf sign t with
    | I.Box(cP, t) ->
       begin match Whnf.rewrite sign cP t with
       | I.SPi (tel, t) -> cP, tel, t
       | _ -> raise (Error.Error ("Lambda abstraction was used in a pattern that did not have "
                                  ^ "syntactic function type but instead had type " ^ IP.print_syn_exp t))
       end
    | t -> raise (Error.Error ("Lambda abstraction was used in a pattern that did not have boxed type but instead had type "
                               ^ IP.print_exp t))
  in
  Debug.print (fun () -> "Split SPi(" ^ IP.print_stel tel ^ ", " ^ IP.print_syn_exp t ^ ")");
  let g', tel0, tel' = theta_of_lam' g xs tel in
  let vs = Syn [I.SPi (tel, t)] in
  let thetatel = [Syntax.Explicit, gen_floating_name (),
                  I.Box(g', if tel' = [] then t else I.SPi (tel', t))] in
  let ws = Syn [I.SPi (tel0, I.SPi(tel', t))] in
  let cD', cT, delta, pdelta, td = split_flex_unify sign [] (Some g) p1 thetatel [p] cD1 vs ws in
  let e = match var_list_of_ctx td with
    | [e] -> e
    | _ -> raise (Error.Violation ("Split_lam obtained more than one parameter out of td (" ^ print_ctx td ^ ")"))
  in
  let xs' = List.map2 (fun x (_,_,t) -> x, t) xs tel0 in
  let ss = x, I.TermBox (g, I.Lam (xs', I.Unbox(e, I.id_sub, bctx_from_lam g xs'))) in
  let p' = match simul_syn_psubst_on_list sign g pdelta (punbox_list_of_ctx g cT) with
    | [p'] -> p'
    | _ -> raise (Error.Violation ("Split_lam obtained more than one parameter out of substituting in cT"))
  in
  let pss = x, I.PTBox(g, I.PLam (xs', p')) in
  let res = compute_split_map sign ss pss cD1 x cD2 delta pdelta cD' in
  Debug.deindent (); res

let split_const (sign : signature) (p1 : pats) (c, ps : def_name * pats)
                (cD1 : ctx) (x, t : name * I.exp) (cD2 : ctx) : ctx * I.pats =
  Debug.indent ();
  Debug.print (fun () -> "Splitting on constructor " ^ c ^ "\nSplit type " ^ IP.print_exp t) ;
  Debug.print (fun () -> "wtf? : " ^ print_ctx cD1);
  let maybe_g, n, sp =
    match Whnf.whnf sign t with
    | I.App(I.Const n, sp) -> None, n, Comp sp
    | I.Const n -> None, n, Comp []
    | I.Box(cP, t) ->
       begin match Whnf.rewrite sign cP t with
       | I.SConst n -> Some cP, n, Syn []
       | I.AppL (h, sp) ->
          begin match Whnf.rewrite sign cP h with
          | I.SConst n -> Some cP, n, Syn sp
          | e -> raise (Error.Error ("Expected constructor application. Got " ^ IP.print_syn_exp e))
          end
       | e -> raise (Error.Error ("Expected constructor application. Got " ^ IP.print_syn_exp e))
       end
    | e -> raise (Error.Error ("Expected constructor application. Got " ^ IP.print_exp e))
  in
  let get_cP = function
    | Some cP -> cP
    | None -> raise (Error.Error "Syntactic constructor was used in pattern that was not of boxed type")
  in
  let thetatel, (n', sp') = if is_syn_con sign c then
                              let thetatel, (n', sp') = lookup_syn_cons_entry sign c (get_cP maybe_g) in
                              thetatel, (n', Syn sp')
                            else
                              let thetatel, (n', sp') = lookup_cons_entry sign c in
                              thetatel, (n', Comp sp')
  in

  Debug.print (fun () -> "thetatel = " ^ IP.print_tel thetatel);
  if n = n'
  then
    let cD1, sigma, us, vs, ws = split_idx_param sign cD1 n sp sp' in
    Debug.print (fun () -> "wtf? : " ^ print_ctx cD1);
    let cD', cT, delta, pdelta, td = split_flex_unify sign sigma maybe_g p1 thetatel ps cD1 vs ws in
    let ss = if is_syn_con sign c then
               let cP = get_cP maybe_g in
               x, I.TermBox(cP, I.AppL (I.SConst c, unbox_list_of_ctx cP td))
             else
               x, I.App (I.Const c, var_list_of_ctx td) in
    let pss = if is_syn_con sign c then
               let cP = get_cP maybe_g in
               x, I.PTBox(cP, I.PSConst (c, simul_syn_psubst_on_list sign cP pdelta (punbox_list_of_ctx cP cT)))
             else
               x, I.PConst (c, simul_psubst_on_list sign pdelta (pvar_list_of_ctx cT)) in
    let res = compute_split_map sign ss pss cD1 x cD2 delta pdelta cD' in
    Debug.deindent (); res
  else
    raise (Error.Error ("Get a grip!, wrong constructor. n = \"" ^ n ^ "\"; n' = \"" ^ n' ^ "\""))

let check_ppar (sign : signature) (p1 : pats) (n : name) (cD1 : ctx)
    (x, t : name * I.exp) (cD2 : ctx) : ctx * I.pats =
  let g, t = match Whnf.whnf sign t with
    | I.Box (I.Nil, t) -> raise (Error.Error "Matched on a parameter variable when context was expected to be empty")
    | I.Box (g, t) -> g, t
    | t -> raise (Error.Error ("Parameter variables can only be used against a boxed type. Found " ^ IP.print_exp t))
  in

  compute_split_map sign (x, I.Var n) (x, I.PPar n) cD1 x cD2 [] [] (cD1 @ [n, I.Box (g, t)])
  (* (\* let cD' = cD1 @ [n, Box (g, t)] @ (simul_subst_on_ctx [x, Var n] cD2) in *\) *)
  (* let delta =  *)

let split_clos (sign : signature) (p1 : pats) (n, s : name * pat_subst) (cD1 : ctx)
    (x, t : name * I.exp) (cD2 : ctx) : ctx * I.pats =
  let cP, t = match Whnf.whnf sign t with
    | I.Box(cP, t) -> cP, t
    | t -> raise (Error.Error ("Substitution on a pattern variable can "
                               ^ "only be used against a boxed type. Found "
                               ^ IP.print_exp t))
  in
  let rec subst_of_pat_subst = function
    | CShift n -> I.Shift n
    | CEmpty -> I.Empty
    | CDot(s, i) -> I.Dot(subst_of_pat_subst s, I.BVar i)
  in
  match Whnf.apply_inv t s with
  | Some t -> let cP' = get_domain cP s in
              compute_split_map sign (x, I.TermBox (cP, I.Unbox(I.Var n, subst_of_pat_subst s, cP')))
                                (x, I.PTBox(cP, I.PUnbox(n, s, cP')))
                                cD1 x cD2 [] [] (cD1 @ [n, I.Box (cP', t)])
  | None -> raise (Error.Error ("Cannot check pattern matching clause " ^ print_name n ^ "[" ^ print_pat_subst s ^ "] "
                               ^ " because it was not possible to compute an inverse substitution for " ^ print_pat_subst s))

let split_rec (sign : signature) (ps : pats) (cD : ctx) : ctx * I.pats =
  let rec search p1 p2 cD1 cD2 =
    match p2 with
    | Apx p :: ps -> search_apx p1 p ps cD1 cD2

    | Int p :: ps -> search_int p1 p ps cD1 cD2
    | [] -> raise (Error.Violation ("Search concluded and didn't choose a pattern to split on."))
  and search_apx p1 p ps cD1 cD2 =
    match p, cD2 with
    | A.PConst (c, sp), (x, t) :: cD2 ->
       split_const sign p1 (c, List.map (fun p -> Apx p) sp) cD1 (x, t) cD2

    | A.PVar y, (x, t) :: cD2 ->
       search (p1 @ [Apx(A.PVar y)]) ps (cD1 @ [y, t]) (ctx_subst (x, I.Var y) cD2)

    | A.Innac e, (x, t) :: cD2 ->
       search (p1 @ [Apx(A.Innac e)]) ps (cD1 @ [x, t]) cD2
    | A.PPar y, (x, t) :: cD2 ->
       check_ppar sign p1 y cD1 (x, t) cD2
    | A.PClos (y, s), (x, t) :: cD2 ->
       split_clos sign p1 (y, s) cD1 (x, t) cD2
    | A.SInnac (e, s), (x, t) :: cD2 ->
       search (p1 @ [Apx(A.SInnac (e, s))]) ps (cD1 @ [x, t]) cD2
    | A.PLam (xs, p), (x, t) :: cD2 ->
       split_lam sign p1 (xs, Apx p) cD1 (x, t) cD2

    | _ -> raise (Error.Error ("Search: not implemented\np = " ^ AP.print_pat p ^ "\ncD2 = " ^ print_ctx cD2))

  and search_int p1 p ps cD1 cD2 =
    match p, cD2 with
    | I.PVar y, (x, t) :: cD2 ->
       search (p1 @ [Int(I.PVar y)]) ps (cD1 @ [y, t]) (ctx_subst (x, I.Var y) cD2)
    | I.Innac e, (x, t) :: cD2 ->
       search (p1 @ [Int(I.Innac e)]) ps (cD1 @ [x, t]) cD2
    | I.PTBox (cP1, I.PUnbox(n, s, cP2)), (x, t) :: cD2 ->
       search (p1 @ [Int(I.PTBox (cP1, I.PUnbox(n, s, cP2)))]) ps (cD1 @ [x, t]) cD2
    | _ -> raise (Error.Violation ("I bet this will never be raised. p = " ^ IP.print_pat p))
  (*   match p, cD2 with *)
  (*   | I.PConst (c, sp), (x, t) :: cD2 -> *)
  (*      split_const sign p1 (c, List.map (fun p -> Int p) sp) cD1 (x, t) cD2 *)

  (*   | I.PVar y, (x, t) :: cD2 -> *)
  (*      search (p1 @ [Int(I.PVar y)]) ps (cD1 @ [y, t]) (ctx_subst (x, I.Var y) cD2) *)

  (*   | I.Innac e, (x, t) :: cD2 -> *)
  (*      search (p1 @ [Int(I.Innac e)]) ps (cD1 @ [x, t]) cD2 *)
  (*   | I.PPar y, (x, t) :: cD2 -> *)
  (*      check_ppar sign p1 y cD1 (x, t) cD2 *)
  (*   | I.PTBox(cP, p), cD2 -> *)
  (*      search_syn_int cP p1 p ps cD1 cD2 *)

  (*   | _ -> raise (Error.Error ("Search: not implemented(int)\np = " ^ IP.print_pat p ^ "\ncD2 = " ^ print_ctx cD2)) *)

  (* and search_syn_int cP p1 p ps cD1 cD2 = *)
  (*   match p, cD2 with *)
  (*   | I.PSConst (c, sp), (x, t) ::cD2 -> *)
  (*      assert false *)


  (*   | _ -> raise (Error.Error ("Search: Syntax not implemented\np2 = " ^ AP.print_pat p ^ "\ncD2 = " ^ print_ctx cD2)) *)
  in
  search [] ps [] cD

let split_set sign (x : name) (cG : ctx) : I.pats =
  let rec f = function
    | [] -> raise (Error.Violation ("Variable " ^ print_name x ^ " appears free in context for pattern matching split."))
    | (x', t) :: cG' when x = x' -> [], t, cG'
    | (y, t) :: cG' -> let cG2, t', cG1 = f cG' in ((y, t) :: cG2), t', cG1
  in
  let cG2, t, cG1 = f cG in
  match Whnf.whnf sign t with
  | I.App(I.Const n, sp) ->
     let constrs = lookup_constructors sign n in
     let rec split_constrs constrs =
       begin match constrs with
       | [] -> []
       | c :: constrs' ->
          let thetatel, (n', sp) = lookup_cons_entry sign c in
          let ps = (inac_ctx cG2) @ [I.PConst (c, inac_ctx (ctx_of_tel thetatel))] @ (inac_ctx cG1) in
          let sigma =
            try
              snd (split_rec sign (List.map (fun p -> Int p) ps) (cG2 @ [(x, t)] @ cG1))
            with
            | Unify.Unification_failure _ -> []
          in
          sigma @ (split_constrs constrs')
       end
     in
     split_constrs constrs

  | _ -> raise (Error.Error ("Type " ^ IP.print_exp t ^ " should be a data type."))

let refine (sign : signature) (p : pats) (cD : ctx) (sigma : I.pats) : pats * ctx * I.pats =
  Debug.indent ();
  Debug.print (fun () -> "Refined called: p = " ^ print_pats p
                         ^ "\ncD = " ^ print_ctx cD
                         ^ "\nsigma = " ^ IP.print_pats sigma);
  let cD', delta = split_rec sign p cD in
  Debug.print (fun () -> "Calling split_rec with cD = " ^ print_ctx cD
                         ^ "\np = " ^ print_pats p
                         ^ "\nresulting in delta = " ^ IP.print_pats delta
                         ^ "\nand ctx cD' = " ^ print_ctx cD' ^ ".");
  let p' = matchings delta p in
  Debug.print (fun () -> "Calling matchings with delta = " ^ IP.print_pats delta
                         ^ "\np = " ^ print_pats p ^ "\nresulting in " ^ print_pats p' ^ ".");
  let sd = compose_maps sign sigma cD delta in
  Debug.deindent ();
  p' , cD', sd

let check_pats (sign : signature) (p : pats) (cG : ctx) : ctx * I.pats =
  Debug.indent ();
  let is_Pvar = function
    | Int (I.PVar _)
    | Int (I.PTBox (_, I.PUnbox(_, _, _)))
    | Apx (A.SInnac (_, _))
    | Apx (A.PVar _) -> true
    | _ -> false
  in
  let rec unify_names p cG =
    match p, cG with
    | [], [] -> []
    | Int (I.PVar x) :: p', (y, t) :: cG' when x <> y -> (x, t) :: (compose_single_with_subst (y, I.Var x) (unify_names p' cG'))
    | Apx (A.PVar x) :: p', (y, t) :: cG' when x <> y -> (x, t) :: (compose_single_with_subst (y, I.Var x) (unify_names p' cG'))
    | _ :: p', s :: cG' -> s :: (unify_names p' cG')
    | _ -> raise (Error.Violation "Length error in unify names")
  in
  let cG' = unify_names p cG in
  let cG = cG' in
  let rec check_pats (p : pats) (sigma : I.pats) (cD : ctx) : ctx * I.pats =
    if List.for_all is_Pvar p then
      cD, sigma
    else
      let p', cD', sigma' = refine sign p cD sigma in
      Debug.print (fun () -> "Check pats on"
                             ^ "\np = " ^ print_pats p
                             ^ "\nsigma = " ^ IP.print_pats sigma
                             ^ "\ncD = " ^ print_ctx cD);
      Debug.print (fun () -> "Getting from refine"
                             ^ "\np' = " ^ print_pats p'
                             ^ "\nsigma' = " ^ IP.print_pats sigma'
                             ^ "\ncD' = " ^ print_ctx cD');

      check_pats p' sigma' cD'
  in
  let res = check_pats p (List.map (fun (x, _) -> I.PVar x) cG) cG in
  Debug.deindent ();
  res

let rec check_inacs (sign, cD : signature * ctx) (p : A.pats) (sigma : I.pats) (cG : ctx) : I.pats =
  match p, sigma with
  | p::ps, q::qs ->
     begin match cG with
     | (x, t) :: cG' ->
        let p' = check_inac (sign, cD) p q t in
        p' :: check_inacs (sign, cD) ps qs (ctx_subst (x, exp_of_pat sign p') cG')
     | _ -> raise (Error.Error "The context ended unexpectedly.")
     end
  | [], [] -> []
  | _ -> raise (Error.Error "Size mismatch.")

and check_inacs_syn (sign, cD : signature * ctx) (cP : I.bctx) (p : A.pats) (sigma : I.syn_pats) (tel : I.stel) : I.syn_pats =
  let rec make_subst_tel ps qs tel cP' s =
    match ps, qs with
    | p::ps, q::qs ->
       begin match tel with
       | (_, x, t)::tel' ->
          let p' = check_inac_syn (sign, cD) cP p q (I.Clos (t, s, cP')) in
          let s' = I.Dot(s, syn_exp_of_pat sign p') in
          p' :: (make_subst_tel ps qs tel' (I.Snoc (cP', x, t)) s')
       | _ -> raise (Error.Error "The context ended unexpectedly.")
       end
    | [], [] -> []
    | _ -> raise (Error.Error "Size mismatch.")
  in make_subst_tel p sigma tel cP I.id_sub

and check_inac (sign, cD : signature * ctx) (p : A.pat) (q : I.pat) (t : I.exp) : I.pat =
  match p, q with
  | A.Innac ep, I.Innac eq ->
     Debug.indent ();
     let ep' = check (sign, cD) ep t in
     let _, sigma = try Unify.unify (sign, cD) ep' eq
             with Unify.Unification_failure prob ->
               raise (Error.Error ("Inaccessible pattern check failed with:\n" ^ Unify.print_unification_problem prob))
     in
     Debug.deindent ();
     I.Innac (simul_subst sigma ep')
  | A.PVar x, I.PVar y when x = y -> I.PVar x
  | A.PPar x, I.PPar y when x = y -> I.PPar x
  | A.PConst (n, sp), I.PConst (n', sq) when n = n' ->
     begin match lookup_sign_entry sign n with
     | Constructor (_, tel, _) -> I.PConst (n, check_inacs (sign, cD) sp sq (ctx_of_tel tel))
     | SConstructor (_, stel, _) -> (* raise (Error.Violation ("Syntactic constructor used with PConst")) *)
        let cP = match t with
          | I.Box(cP, _) -> cP
          | _ -> raise (Error.Violation ("Syntactic constructor was used to split on a non boxed type"))
        in
        let f = function
          | [] -> []
          | _ -> Debug.print (fun() -> "SQ(pigs) are: " ^ IP.print_pats sq); assert false
        in
        let sq' = f sq in
        I.PTBox(cP, I.PSConst (n, check_inacs_syn (sign, cD) cP sp sq' stel))
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | _, I.PTBox (cP, q) -> begin match t with
         | I.Box (cP', t') when cP = cP' -> I.PTBox(cP, check_inac_syn (sign, cD) cP p q t')
         | _ -> raise (Error.Error ("Syntactic pattern was used against a non boxed type: " ^ Pretty.print_exp (sign, cD) t))
         end
  | _ -> raise (Error.Violation "Not implemented")

and check_inac_syn (sign, cD : signature * ctx) (cP : I.bctx) (p : A.pat) (q : I.syn_pat) (t : I.syn_exp) : I.syn_pat =
  match p, q with
  | A.PConst (n, sp), I.PSConst (n', sq) when n = n' ->
     begin match lookup_sign_entry sign n with
     | Constructor (_, tel, _) -> raise (Error.Error ("Used a data type constructor inside a syntactic pattern"))
     | SConstructor (_, tel, _) ->
        I.PSConst (n, check_inacs_syn (sign, cD) cP sp sq tel)
     | _ -> raise (Error.Violation ("It should have been a constructor."))
     end
  | A.PLam (xs, p), I.PLam (ys, q) ->
     if List.length xs = List.length ys then
       let tel, t = begin match Whnf.rewrite sign cP t with
                       | I.SPi (tel, t) -> tel, t
                       | t -> raise (Error.Violation ("Match - check_inac - PLam should have boxed spi type. Instead got "
                                                      ^ IP.print_syn_exp t))
                       end
       in
       let cP', _, tel' = theta_of_lam cP xs tel in
       I.PLam (ys, check_inac_syn (sign, cD) cP' p q (if tel' = [] then t else I.SPi (tel', t)))
     else
       raise (Error.Violation "Match - check_inac - PLam binding sizes differ. Who knows why?")
  | A.PClos (n, s), I.PUnbox (n', s', cP') when n = n' && s = s' ->
     I.PUnbox(n, s', cP')
  | A.PVar n, I.PUnbox (n', CShift 0, cP') when n = n' ->
     I.PUnbox(n, CShift 0, cP')
  | A.PBVar i, I.PBVar i' when i = i' ->
     I.PBVar i

  (* In the syntax cases, we might need to grow cP *)
  | p, q -> raise (Error.Error ("Pattern matching on this syntax term is not yet supported.\np = "
                                ^ AP.print_pat p ^ "\nq = " ^ IP.print_syn_pat q))

let check_lhs (sign : signature) (p : A.pats) (cG : ctx) : ctx * I.pats =
  let p' = proc_pats p in
  let cD, sigma = check_pats sign p' cG in
  Debug.print (fun () -> "Checking inacessible patterns.\ncG = " ^ print_ctx cG
    ^ "\np = " ^ print_pats p' ^ "\nsigma = " ^ IP.print_pats sigma);
  let sigma' = check_inacs (sign, cD) p sigma cG in
  cD, sigma'

let caseless (sign : signature) (cD : ctx) (x : name) (t : I.exp) : unit =
  if [] = (* snd(split sign [PVar x] ((x, t) :: cD)) *) assert false
  then ()
  else raise (Error.Error ("Pattern variable " ^ print_name x ^ " is not really impossible."))

let check_clause (sign : signature) (f : def_name) (p : A.pats) (telG : I.tel) (t : I.exp) (rhs : A.rhs) : I.pats * I.rhs =
  Debug.print (fun () -> "Checking pattern clause:\nPattern spine: " ^ AP.print_pats p
    ^ "\nRHS: " ^ AP.print_rhs rhs);
  try
    let cD, sigma = check_lhs sign p (ctx_of_tel telG) in
    Debug.print (fun () -> "LHS was checked:\n cD = " ^ print_ctx cD ^ "\n sigma = "^ IP.print_pats sigma ^ "\n telG = " ^ IP.print_tel telG);
    match rhs with
    | A.Just e ->
      let t' = simul_subst (subst_of_pats sign sigma telG) t in
      Debug.print (fun () -> "Checking RHS " ^ AP.print_exp e ^ " against type " ^ IP.print_exp t' ^ "\nin context " ^ print_ctx cD);
      sigma, I.Just (check (sign, cD) e t')
    | A.Impossible x -> caseless sign cD x t; sigma, I.Impossible x
  with
    Unify.Unification_failure prob ->
    raise (Error.Error ("Check clause failed for definition " ^ f
                        ^ "\nclause: " ^ AP.print_pats p
                        ^ "\nwith unification problem:\n"
                        ^ Unify.print_unification_problem prob))

let check_clauses (sign : signature) (f : def_name) (telG : I.tel) (t : I.exp) (ds : A.pat_decls) : signature * I.pat_decls =
  (* we add a non-reducing version of f to the signature *)
  let sign'=  (Program (f, telG, t, [])) :: sign in
  let ds'= List.map (fun (ps, rhs) -> check_clause sign' f ps telG t rhs) ds  in
  (Program (f, telG, t, ds')) :: sign, ds'

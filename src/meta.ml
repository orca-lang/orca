(* Meta operations on the AST, like substitutions and free vars *)

open Util
open Name
open Print
open Print.Int
open Syntax
open Syntax.Int
open Free

let rec in_ctx n = function
  | (x, _) :: _ when x = n -> true
  | _ :: cG -> in_ctx n cG
  | [] -> false

let rec fv cG =
  let fv e = fv cG e in
  function
  | Set _ -> []
  | Ctx sch -> fv_schema cG sch
  | BCtx cP -> fv_ctx cG cP
  | Pi (tel, t) -> fv_pi cG tel t
  | Box (ctx, e) -> fv_ctx cG ctx @ fv_syn cG e
  | TermBox (ctx, e) -> fv_ctx cG ctx @ fv_syn cG e
  | Fn (xs, e) ->
    List.fold_left (fun vars x -> vars -- x) (fv e) xs
  | App (e1, es) -> fv e1 @ List.concat (List.map fv es)
  | Const n -> []
  | Var n when in_ctx n cG -> []
  | Var n -> [n]
  | Annot (e1, e2) -> fv e1 @ fv e2
  | Hole _ -> []

and fv_syn cG =
  let fvs e = fv_syn cG e in
  function
  | Star -> []
  | SPi (tel, e) -> fv_spi cG tel e
  | Lam (x, e) -> fvs e
  | AppL (e, es) -> fvs e @ List.concat (List.map fvs es)
  | SConst _ -> []
  | BVar i -> []
  | Empty -> []
  | Shift n -> []
  | Dot (e1, e2) -> fvs e1 @ fvs e2
  | Unbox (e, s) ->
    fv cG e @ fvs s
  | SBCtx cP -> fv_ctx cG cP
  | SCtx sch -> fv_schema cG sch
  | Block block -> List.concat (Rlist.mapl (fun (_, t) -> fvs t) block)

and fv_schema cG = function
  | Schema (quant,block) -> List.concat (List.map (fun (_, t) -> fv_syn cG t) quant) 
                            @ List.concat (List.map (fun (_, t) -> fv_syn cG t) block)

and fv_ctx cG = function
  | Nil -> []
  | Snoc(cP, _, e) -> fv_ctx cG cP @ fv_syn cG e
  | CtxVar n when in_ctx n cG -> []
  | CtxVar n -> [n]

and fv_pi cG (tel : tel) (t : exp) = match tel with
  | [] -> fv cG t
  | (_, n, e)::tel -> fv cG e @ (fv_pi cG tel t -- n)

and fv_spi cG (tel : stel) (t : syn_exp) = match tel with
  | [] -> fv_syn cG t
  | (_, n, e)::tel -> fv_syn cG e @ (fv_spi cG tel t)



(* Generate fresh names for all the bound variables,
     to keep names unique *)

let rec refresh_exp (rep : (name * name) list) : exp -> exp =
  let f x = refresh_exp rep x in
  function
  | Set n -> Set n

  | Ctx sch -> Ctx (refresh_schema rep sch)

  | Pi (tel, t) -> let tel', t' = refresh_tel rep tel t in Pi(tel', t')

  | Box (cP, e) -> Box(refresh_bctx rep cP, refresh_syn_exp rep e)
  | TermBox (cP, e) -> TermBox(refresh_bctx rep cP, refresh_syn_exp rep e)
  | BCtx cP -> BCtx (refresh_bctx rep cP)
  | Fn (xs, e) ->
    let xs' = List.map refresh_name xs in
    let extra = List.map2 (fun x y -> x, y) xs xs' in
    Fn (xs', refresh_exp (extra @ rep) e)
  | App (e1, es) -> App(f e1, List.map f es)
  | Const n -> Const n
  | Var n ->
    begin try
        Var (List.assoc n rep)
      with
        Not_found -> Var n
    end
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s

and refresh_syn_exp rep =
  let f x = refresh_syn_exp rep x in
  function
  | Star -> Star
  | SCtx sch -> SCtx (refresh_schema rep sch)
  | SPi (tel, t) -> let tel', t' = refresh_stel rep tel t in SPi(tel', t')
  | Lam (x, e) ->
    Lam(x, f e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar i -> BVar i
  | Empty -> Empty
  | Shift n -> Shift n
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | Unbox (e1, e2) -> Unbox (refresh_exp rep e1, f e2)
  | SBCtx cP -> SBCtx (refresh_bctx rep cP)
  | Block bs -> Block (Rlist.map (fun (n, t) -> (n, f t)) bs)

and refresh_schema rep (Schema (quant,block)) =
  let f (n, t) = (n, refresh_syn_exp rep t) in
  Schema (List.map f quant, List.map f block)

and refresh_bctx (rep : (name * name) list) : bctx -> bctx =
  function
  | Snoc (cP, x, e) -> Snoc (refresh_bctx rep cP, x, refresh_syn_exp rep e)
  | Nil -> Nil
  | CtxVar n ->
    begin try
        CtxVar (List.assoc n rep)
      with
        Not_found -> CtxVar n
    end

and refresh_tel (rep : (name * name) list) (tel : tel) (t : exp) : tel * exp =
  match tel with
  | [] -> [], refresh_exp rep t
  | (i, n, e) :: tel ->
    let n' = refresh_name n in
    let tel', t' = refresh_tel ((n, n')::rep) tel t in
    ((i, n', refresh_exp rep e)::tel'), t'

and refresh_stel (rep : (name * name) list) (tel : stel) (t : syn_exp) : stel * syn_exp =
  match tel with
  | [] -> [], refresh_syn_exp rep t
  | (i, n, e) :: tel ->
    let tel', t' = refresh_stel rep tel t in
    ((i, n, refresh_syn_exp rep e)::tel'), t'

let refresh (e : exp) : exp = refresh_exp [] e

(* refresh one free variable *)
let rec refresh_free_var (x , y : name * name) (e : exp) : exp =
  let f e = refresh_free_var (x, y) e in
  match e with
  | Set n -> Set n
  | Ctx sch -> Ctx (refresh_free_var_schema (x, y) sch)
  | Pi (tel, t) ->
    let tel', t' = refresh_free_var_tel (x, y) tel t in
    Pi (tel', t')
  | Box (cP, e) -> Box(refresh_free_var_bctx (x, y) cP, refresh_free_var_syn (x, y) e)
  | TermBox (cP, e) -> TermBox(refresh_free_var_bctx (x, y) cP, refresh_free_var_syn (x, y) e)
  | BCtx cP -> BCtx (refresh_free_var_bctx (x, y) cP)
  | Fn (xs, _) when List.mem x xs -> raise (Error.Violation "Duplicate variable name")
  | Fn (xs, e) -> Fn (xs, f e)
  | App (e1, es) -> App(f e1, List.map f es)
  | Const n -> Const n
  | Var n when n = x -> Var y
  | Var n -> Var n
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s

and refresh_free_var_syn (x, y) e =
  let f e = refresh_free_var_syn (x, y) e in
  match e with
  | Star -> Star
  | SCtx sch -> SCtx (refresh_free_var_schema (x, y) sch)
  | SPi (tel, t) ->
    let tel', t' = refresh_free_var_stel (x, y) tel t in
    SPi (tel', t')
  | Lam (x, e) -> Lam(x, f e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | BVar i -> BVar i
  | SConst n -> SConst n
  | Unbox (e1, e2) -> Unbox(refresh_free_var (x, y) e1, f e2)
  | Empty -> Empty
  | Shift n -> Shift n
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | SBCtx cP -> SBCtx (refresh_free_var_bctx (x, y) cP)
  | Block cs -> Block (Rlist.map (fun (z, e) -> (z, f e)) cs) (* z has to be free *)

and refresh_free_var_schema (x, y as rep) (Schema (quant, block)) =
  let g (n, t) = (n, refresh_free_var_syn rep t) in
  Schema (List.map g quant, List.map g block)

and refresh_free_var_bctx (x, y) cP =
  match cP with
  | Snoc (cP, z, e2) -> Snoc(refresh_free_var_bctx (x, y) cP , z, refresh_free_var_syn (x, y) e2)
  | Nil -> Nil
  | CtxVar n when n = x -> CtxVar y
  | CtxVar n -> CtxVar n

and refresh_free_var_tel (x, y) tel t =
  match tel with
  | [] -> [], refresh_free_var (x, y) t
  | (i, n, e) :: tel when n = x ->  raise (Error.Violation "Duplicate variable name")
  | (i, n, e) :: tel ->
    let tel', t' = refresh_free_var_tel (x, y) tel t in
    (i, n, refresh_free_var (x, y) e) :: tel', t'
and refresh_free_var_stel (x, y) tel t =
  match tel with
  | [] -> [], refresh_free_var_syn (x, y) t
  | (i, n, e) :: tel ->
    let tel', t' = refresh_free_var_stel (x, y) tel t in
    (i, n, refresh_free_var_syn (x, y) e) :: tel', t'


let refresh_free_vars (rep : (name * name) list) e =
  List.fold_left (fun e (y, y') -> refresh_free_var (y, y') e) e rep

(* Operations on terms *)

(* Substitution of regular variables *)

let fv_subst cG sigma = List.concat (List.map (fun (n, e) -> fv cG e -- n) sigma)

let rec subst (x, es : single_subst) (e : exp) :  exp =
  let f e = subst (x, es) e in
  match e with
  | Set n -> Set n
  | Ctx sch -> Ctx (sub_schema (x, es) sch)
  | Pi (tel, t) ->
    let tel', t' = subst_pi (x, es) tel t in
    Pi(tel', t')
  | Box (ctx, e) -> Box(subst_bctx (x, es) ctx, subst_syn (x, es) e)
  | TermBox (ctx, e) -> TermBox(subst_bctx (x, es) ctx, subst_syn (x, es) e)
  | BCtx cP -> BCtx(subst_bctx (x, es) cP)
  | Fn (ys, e) ->
    let ys' = List.map refresh_name ys in
    (* the following cannot happen because y' is just fresh *)
    (* if List.mem y' (fv es) then raise (Error.Violation
       "Duplicate variable name would be captured.") ; *)
    let extra = List.map2 (fun x y -> x, y) ys ys' in
    Fn(ys', subst (x, es) (refresh_free_vars extra e))

  | App (e1, es) -> App(f e1, List.map f es)
  | Const n -> Const n
  | Var n  when x = n -> refresh es
  | Var n -> Var n
  | Annot (e1, e2) -> Annot(f e1, f e2)
  | Hole s -> Hole s

and sub_schema s (Schema (quant, block)) =
  let g (n, e) = (n, subst_syn s e) in
  Schema (List.map g quant, List.map g block)

and subst_syn (x, es) e =
  let f e = subst_syn (x, es) e in
  match e with
  | Star -> Star
  | SCtx sch -> SCtx (sub_schema (x, es) sch)
  | SPi (tel, t) ->
    let tel', t' = subst_spi (x, es) tel t in
    SPi(tel', t')
  | Lam (x, e) -> Lam(x, f e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar i -> BVar i
  | Unbox (e1, e2) -> Unbox(subst (x, es) e1, f e2)
  | Empty -> Empty
  | Shift n -> Shift n
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | SBCtx cP -> SBCtx (subst_bctx (x, es) cP)
  | Block cs -> Block (subst_block (x, es) cs)

and subst_bctx (x, es : single_subst) cP =
  match cP with
  | Snoc (e1, y, e2) -> Snoc (subst_bctx (x, es) e1, y, subst_syn (x, es) e2)
  | Nil -> Nil
  | CtxVar n when x = n ->
    begin match es with
      | BCtx cP -> refresh_bctx [] cP
      | Var y -> CtxVar y
      | e -> raise (Error.Violation ("I don't believe you! " ^ print_exp e))
    end
  | CtxVar n -> CtxVar n

and subst_block (x, es : single_subst) cP =
  let open Rlist in match cP with
  | RCons (l, (y, e)) -> RCons (subst_block (x, es) l, (y, subst_syn (x, es) e))
  | RNil -> RNil

and subst_pi (x, es) tel t =
  match tel with
  | [] -> [], subst (x, es) t
  | (i, n, e) :: tel ->
    let n' = refresh_name n in
    (* the following cannot happen because n' is just fresh *)
    (* if List.mem n' (fv es) then raise (Error.Violation "Duplicate variable name would be captured.") ; *)
    let tel', t' = refresh_free_var_tel (n, n') tel t in
    let tel'', t'' = subst_pi (x, es) tel' t' in
    (i, n', subst (x, es) e) :: tel'', t''
and subst_spi (x, es) tel t =
  match tel with
  | [] -> [], subst_syn (x, es) t
  | (i, n, e) :: tel ->
    let tel', t' = subst_spi (x, es) tel t in
    (i, n, subst_syn (x, es) e) :: tel', t'

let simul_subst sigma e =
  List.fold_left (fun e s -> subst s e) e sigma

let simul_subst_syn sigma e =
  List.fold_left (fun e s -> subst_syn s e) e sigma

let simul_subst_on_list sigma l =
  List.map (fun e -> simul_subst sigma e) l

let simul_subst_syn_on_list sigma l =
  List.map (fun e -> simul_subst_syn sigma e) l

let simul_subst_on_tel sigma tel =
  List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

let simul_subst_on_stel sigma tel =
  List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

let simul_subst_on_bctx sigma cP =
  List.fold_left (fun cP s -> subst_bctx s cP) cP sigma

let rec compose_single_with_subst s = function
  | [] -> []
  | (y, t') :: sigma -> (y, subst s t') :: (compose_single_with_subst s sigma)

let compose_subst sigma delta = List.map (fun (x, t) -> x, simul_subst sigma t) delta

let rec subst_of_pats sign (sigma : pats) (tel : tel) : subst =
  match sigma, tel with
  | [], [] -> []
  | p :: ps, (_, n, t) :: tel' -> (n, exp_of_pat p) :: (subst_of_pats sign ps tel')
  | _ -> raise (Error.Violation "subst_of_ctx_map got lists of different lengths")

let ctx_of_tel (tel : tel) : ctx = List.rev (List.map (fun (_, x, s) -> x, s) tel)

let exp_list_of_ctx : ctx -> exp list = List.map snd

let subst_of_ctx : ctx -> subst = List.map (fun (x, _) -> x, Var x)

let name_list_of_ctx : ctx -> name list = List.map fst

let var_list_of_ctx : ctx -> exp list = List.map (fun (x, _) -> Var x)

let var_list_of_tel : tel -> exp list = List.map (fun (_, x, _) -> Var x)

let unbox_list_of_ctx : ctx -> syn_exp list = List.map (fun (x, _) -> Unbox(Var x, id_sub))
let punbox_list_of_ctx : ctx -> syn_pat list = List.map (fun (x, _) -> PUnbox(x, pid_sub))
let unbox_list_of_tel : tel -> syn_exp list = List.map (fun (_, x, _) -> Unbox(Var x, id_sub))
let punbox_list_of_tel : tel -> syn_pat list = List.map (fun (_, x, _) -> PUnbox(x, pid_sub))

(* Re-orders variables to satisfy dependencies *)
(* TODO have a nicer algorithm *)
let topologic_ctx (cG0 : ctx) : ctx =
  let rec topo cG cD acc =
    match cG with
    | [] -> cD, acc
    | (x, t) :: cG -> 
      if fv cD t = [] then
        topo cG ((x, t) :: cD) acc
      else
        topo cG cD ((x, t) :: acc)  
  in
  let rec tries cD cG = 
    let cD', cG' = topo cG cD [] in
    if cG' = [] then
      cD'
    else if List.length cD < List.length cD' then
      tries cD' cG'
    else 
      raise (Error.Error ("No topological order found for context\n" ^ Pretty.print_ctx cG0 ^ "\n Leftover variables are\n" ^ Pretty.print_ctx cG'))
  in tries [] cG0

let ctx_subst s cG =
  let rec ctx_subst s = function
    | (x, t) :: cG -> (x, subst s t) :: (ctx_subst s cG)
    | [] -> []
  in
  let cG' = ctx_subst s cG in
  topologic_ctx cG'    

let ctx_var_subst (x, y) cG =
  let rec replace_var_in_subst (x, y) = function
    | (z, t) :: cG when x = z -> (y, t) :: replace_var_in_subst (x, y) cG
    | (z, t) :: cG  -> (z, t) :: replace_var_in_subst (x, y) cG
    | [] -> []
  in
  ctx_subst (x, Var y) (replace_var_in_subst (x, y) cG)

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

let lookup_ctx_fail cG n =
  match lookup_ctx cG n with
  | None -> raise (Error.Violation
                     ("Unbound var after preprocessing, this cannot happen. (Var: "
                      ^ print_name n ^ ")"))
  | Some t -> t

let rec rename_ctx_using_subst (cG : ctx) (sigma : subst) =
  match cG with
  | [] -> []
  | (x, t) :: cG' ->
    match lookup_ctx sigma x with
    | Some (Var y) -> (y, t) :: (rename_ctx_using_subst cG' sigma)
    | _ -> (x, t) :: (rename_ctx_using_subst cG' sigma)

let print_subst sigma = "[" ^ String.concat ", " (List.map (fun (x, e) -> print_exp e ^ "/" ^ print_name x) sigma) ^ "]"


(* Operations on patterns *)

let bctx_of_lam_pars cP xs = List.fold_left (fun cP (x, t) -> Snoc(cP, x, t)) cP xs

(* Substitution utilities *)

let rec wkn_pat_subst_by_n s =
  let rec shift = function
    | CShift n -> CShift (n+1)
    | CEmpty -> CEmpty
    | CDot (s, n) -> CDot (shift s, (fst n+1, snd n))
  in
  function
  | 0 -> s
  | n -> wkn_pat_subst_by_n (CDot (shift s, zidx)) (n-1)

let rec lookup_pat_subst err i s = match i, s with
  | (0, _), CDot (_, j) -> j
  | i, CDot (s', _) -> lookup_pat_subst err (dec_idx i) s'
  | i, CShift n -> shift_idx i n
  | i, CEmpty -> raise (Error.Error err)

let rec comp_pat_subst err s s' =
  match s, s' with
  | CShift n, CShift n' -> CShift (n + n')
  | _, CEmpty -> CEmpty
  | CEmpty, CShift _ -> raise (Error.Error err)
  | CEmpty, CDot _ -> raise (Error.Error err)
  | s, CDot(s', x) ->
    CDot(comp_pat_subst err s s', lookup_pat_subst err x s)
  | CDot (s', x), CShift n -> comp_pat_subst err s' (CShift (n-1))

type single_psubst = name * pat
type psubst = single_psubst list

let rec psubst (x, p') = function
  | PVar n when n = x -> p'
  | PVar n -> PVar n
  | Inacc e -> Inacc (subst (x, exp_of_pat p') e)
  | PConst (n, ps) -> PConst (n, List.map (psubst (x, p')) ps)
  | PBCtx cP -> PBCtx (bctx_psubst (x, p') cP)
  | PUnder -> PUnder
  | PTBox (cP, p) -> let cP' = subst_bctx (x, exp_of_pat p') cP in
    PTBox (cP', syn_psubst cP' (x, p') p)
and syn_psubst cP (x, p') = function
  | PBVar i -> PBVar i
  | PLam (xs, p) -> PLam (xs, syn_psubst (bctx_of_lam_pars cP xs) (x, p') p) (* What about shifts in p'? *)
  | PSConst (n, ps) -> PSConst (n, List.map (syn_psubst cP (x, p')) ps)
  | PUnbox (n, s) when n = x ->
    begin match p' with
      | PVar m -> PUnbox (m, s)
      | Inacc e -> SInacc (e, s)
      | PTBox (cP'', q) ->  (* cP' should be equal to cP'' *)
        let rec push_unbox s = function
          | PBVar i ->
            PBVar (lookup_pat_subst ("Expected term " ^ print_syn_pat q ^ " to be closed") i s)
          | PLam (xs , p) -> PLam(xs, push_unbox (wkn_pat_subst_by_n s (List.length xs)) p)
          | PSConst (n,ps) -> PSConst (n, List.map (push_unbox s) ps)
          | PUnbox (m, s') ->
            PUnbox (m, comp_pat_subst ("Mismatching substitution from term " ^ print_syn_pat q) s s')
          | SInacc (e, s') ->
            SInacc (e, comp_pat_subst ("Mismatching substitution from term " ^ print_syn_pat q) s s')
          | PEmpty  -> PEmpty
          | PShift n ->
            let rec comp s n =
              match s, n with
              | _, 0 ->
                let rec convert = function
                  | CEmpty -> PEmpty
                  | CShift n -> PShift n
                  | CDot (s, i) -> PDot (convert s, PBVar i)
                in
                convert s
              | CDot (s', _), _ -> comp s' (n-1)
              | CShift n', _ -> PShift (n+n')
              | CEmpty, _ -> raise (Error.Error ("Empty substitution applied to a shift."))
            in
            comp s n
          | PDot (sigma, p) -> PDot (push_unbox s sigma, push_unbox s p)
          | PPar (n, pr) -> PPar (n, pr)

        in
        push_unbox s q
      | _ -> assert false
    end
  | PUnbox (n, s) -> PUnbox (n, s)
  | SInacc (e, s) -> SInacc (subst (x, exp_of_pat p') e, s)
  | PEmpty -> PEmpty
  | PShift n -> PShift n
  | PDot (s, p) -> PDot (syn_psubst cP (x, p') s, syn_psubst cP (x, p') p)
  | PPar (n, None) when n = x ->
    begin match p' with
      | PVar m -> PUnbox (m, pid_sub)
      | Inacc e -> SInacc (e, pid_sub)
      | PTBox (cP', PPar (m, pr)) -> PPar (m, pr) (* MMMMMMMM *)
      | _ -> assert false
    end
  | PPar (n, Some _) when n = x -> assert false
  | PPar (n , pr) -> PPar (n, pr)


and bctx_psubst (x, p') = function
  | PNil -> PNil
  | PSnoc (cP, s, t) -> PSnoc (bctx_psubst (x, p') cP, s, subst_syn (x, exp_of_pat p') t)
  | PCtxVar n when n = x ->
    begin match p' with
      | PBCtx p -> p
      | PVar m -> PCtxVar m
      | _ -> raise (Error.Violation ("Why not?" ^ print_pat p'))
    end
  | PCtxVar n -> PCtxVar n

let rec compose_single_with_psubst s = function
  | [] -> []
  | (y, t') :: sigma -> (y, psubst s t') :: (compose_single_with_psubst s sigma)

let pats_of_psubst : psubst -> pats = List.map (fun (x, p) -> p)

let simul_psubst sigma p =
  List.fold_left (fun p s -> psubst s p) p sigma

let simul_syn_psubst cP sigma p =
  List.fold_left (fun p s -> syn_psubst cP s p) p sigma

let simul_psubst_on_list sigma ps =
  List.map (simul_psubst sigma) ps

let simul_syn_psubst_on_list cP sigma ps =
  List.map (simul_syn_psubst cP sigma) ps

let inac_subst e = List.map (fun (x, e) -> x, Inacc e) e
let pvar_list_of_tel : tel -> pats = List.map (fun (_, x, _) -> PVar x)
let punbox_list_of_tel : tel -> syn_pat list = List.map (fun (_, x, _) -> PUnbox(x, pid_sub))
let psubst_of_names e = List.map (fun (n, m) -> n, PVar m) e
let subst_of_names e = List.map (fun (n, m) -> n, Var m) e

let subst_of_psubst sigma = List.map (fun (x, q) -> (x, exp_of_pat q)) sigma

let rec rename (q : pat) (p : Apx.pat) : (name * name) list =
  match q,p with
  | PVar n, Apx.PVar m -> [n, m]
  | PConst (_, qs), Apx.PConst (_, ps) -> rename_all qs ps
  | PBCtx cP, p -> []
  | PUnder, Apx.PUnder -> []
  | PTBox (cP, q), p -> rename_syn q p
  | Inacc (Var n), Apx.PVar m -> [n, m]
  | PVar n, Apx.Inacc (Apx.Var m) -> [n, m]
  | PVar n, Apx.PClos (m, s) -> [n, m]
  | Inacc _, _ -> []                  (* can this be possible? *)
  | _, Apx.Inacc _ -> []                    (* Should we do that here or in a check_inacc function? *)
  (* | PVar n, Apx.PClos (m, s0) -> [n, m] (\* MMMMMMM *\) *)
  | _, Apx.PWildcard -> []
  | _ -> raise (Error.Violation ("2. Renaming of tree node expects matching pattern with tree node\np = " ^ Print.Apx.print_pat p ^"\nq = " ^ print_pat q))

and rename_syn (q : syn_pat) (p : Apx.pat) : (name * name) list =
  match q, p with
  | PBVar _, Apx.PBVar _ -> []
  | PPar (n, _), Apx.PPar (m, _) -> [n, m] (* MMMM might want to compare the projections *)
  | PLam (es, q), Apx.PLam (sl, p) -> rename_syn q p
  | PSConst (_, qs), Apx.PConst (_, ps) -> rename_all_syn qs ps
  | PUnbox (n, _), Apx.PVar m -> [n, m]
  | SInacc _, Apx.Inacc _ -> []
  | PEmpty, Apx.PEmpty -> []
  | PShift _, Apx.PShift _ -> []
  | PDot(sq, q), Apx.PDot (sp, p) -> rename_syn sq sp @ rename_syn q p
  | PUnbox(n, s), Apx.PClos(m, s') -> [n, m]
  | PUnbox(n, s), Apx.Inacc(Apx.Var m) -> [n, m]
  | _, Apx.PWildcard -> []
  | SInacc (e, s), Apx.PVar m ->
    let rec dig = function
      | Var n -> [n, m]
      | TermBox (_, Unbox(e', _)) -> dig e'
      | _ -> raise (Error.Violation "Digging failed")
    in
    dig e
  | _ -> raise (Error.Violation ("1. Renaming of tree node expects matching pattern with tree node\nq = "
                                 ^ print_syn_pat q ^ "\np = " ^ Print.Apx.print_pat p))

and rename_all (qs : pats) (ps : Apx.pats) : (name * name) list = List.concat (List.map2 rename qs ps)

and rename_all_syn (qs : syn_pats) (ps : Apx.pats) : (name * name) list = List.concat (List.map2 rename_syn qs ps)

(* transform a schema part into a stel *)
let impl_to_tel ps = List.map (fun (n, cP, t) -> (Syntax.Implicit, n, Box (cP, t))) ps

let rec impl_to_ctx = function
  | [] -> []
  | (n, cP, t)::ps -> (n, Box(cP, t)) :: impl_to_ctx ps

let simul_subst_in_part sigma ps =
  List.map (fun (n, e) -> n, simul_subst_syn sigma e) ps

(* shift all variables by n *)
let rec weaken_syn n t = 
let f = weaken_syn n in 
match t with
  | Star -> Star
  | SCtx sch -> SCtx sch 
  | SPi (tel, t) -> assert false
  | Lam (xs, e) -> assert false
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar (i, o) -> BVar (i + n, o)
  | Unbox (e, s) -> Unbox(e, f s)
  | Empty -> Empty
  | Shift n' -> Shift (n + n')
  | Dot (s, e) -> Dot (f s, f e)
  | SBCtx cP -> assert false
  | Block cs -> assert false

(* Shifts all variables except the top n *)
let rec shiftS_syn n t =
if n = 0 then t else Dot (weaken_syn (n-1) t, i0)

let rec apply_syn_subst (sigma : syn_exp) (t : syn_exp) : syn_exp = 
let f = apply_syn_subst sigma in match t with
  | Star -> Star
  | SCtx sch -> SCtx sch (*MMMMM*)
  | SPi (tel, t) -> 
    let tel', sigma' = apply_syn_subst_stel sigma tel in
    SPi (tel', apply_syn_subst sigma' t)
  | Lam (xs, e) -> 
    let xs', sigma' = apply_syn_subst_lam sigma xs in
    Lam (xs', apply_syn_subst sigma' e)
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar i -> BVar i
  | Unbox (e1, e2) -> Unbox(e1, f e2)
  | Empty -> Empty
  | Shift n -> Shift n
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | SBCtx cP -> assert false
  | Block cs -> assert false
 
and apply_syn_subst_stel sigma = function
| [] -> [], sigma
| (icit, x, t)::stel -> 
  let el = (icit, x, apply_syn_subst sigma t) in
  let sigma' = shiftS_syn 1 sigma in
  let stel', sigma'' = apply_syn_subst_stel sigma' stel in
  el::stel', sigma''

and apply_syn_subst_lam sigma = function
| [] -> [], sigma
| (x, t)::xs -> 
  let el = (x, apply_syn_subst sigma t) in
  let sigma' = shiftS_syn 1 sigma in
  let xs', sigma'' = apply_syn_subst_lam sigma' xs in
  el::xs', sigma''

(* generate meta variables for all the quantifiers in a schema and apply them to the block (generates a new block) *)
let mk_quant_subst cP quant block = 
  let rec mk_subst = function
    | [] -> Empty, cP, []
    | (x, t) :: quant -> 
      let x' = Name.gen_name x in
      Debug.print (fun () -> "mk_quant_subst generates new name: " ^ print_name x');
      let sigma, cP', flex = mk_subst quant in
      Dot (sigma, Unbox(Var x', id_sub)), Snoc(cP', x, apply_syn_subst sigma t), x'::flex
  in
  let sigma, cP', flex = mk_subst quant in
  let rec subst_schema cP' sigma = function
    | [] -> []
    | (x, t) :: block -> 
      let t' = apply_syn_subst sigma t in
      (x, t') :: subst_schema (Snoc(cP', x, t')) (Dot(sigma, BVar (0,None))) block
  in
  let block' = subst_schema cP sigma block in
  block', flex

(* Utilities *)

let rec append_bctx cP cP' =
  match cP with
  | Nil -> cP'
  | CtxVar _ -> raise (Error.Violation "Appended a bctx terminating with a CtxVar to another bctx")
  | Snoc (cP, x, e) -> Snoc (append_bctx cP cP', x, e)

let lookup_bound_name cP x =
  let rec lookup cP0 i =
    match cP0 with
    | Snoc (_, x', t) when x = x' -> i, apply_syn_subst (Shift (i+1)) t
    | Snoc (cP', _, _) -> lookup cP' (i+1)
    | _ -> raise (Error.Error ("Bound variable " ^ x ^ " not found in bound context"))
  in
  lookup cP 0

let lookup_bound cP (x, j) =
  let proj x = function
    | Block bs, Some j' -> 
      let rec mk_subst = function
      | n when n = j' -> Shift (x+1)
      | n -> Dot(mk_subst (n+1), BVar (x, Some n)) 
      in
      apply_syn_subst (mk_subst 0) (snd (Rlist.nth (Rlist.rev bs) j'))
    | t, None -> apply_syn_subst (Shift (x+1)) t
    | _ -> raise (Error.Error "Projection of something that is not a block.")
  in
  let rec lookup cP0 i =
    match cP0 with
    | Snoc (_, _, t) when i = 0 -> proj x (t, j)
    | Snoc (cP', _, _) -> lookup cP' (i-1)
    | _ -> raise (Error.Error ("Bound variable had index larger than bound context"))
  in
  lookup cP x

let rec bctx_of_lam_stel (fs : string list) (tel : stel) (cP : bctx) : bctx * stel=
  match fs, tel with
  | [], tel' -> cP, tel'
  | f::fs', (_, _, t)::tel' ->
    let cP, tel'' = bctx_of_lam_stel fs' tel' cP in
    Snoc (cP , f, t), tel''
  | _, [] -> raise (Error.Error ("Too many variables declared in lambda"))

let bctx_of_stel cP tel =
  let rec make = function
    | [] -> cP
    | (_, x, s)::tel' -> Snoc (make tel', x, s)
  in
  make (List.rev tel)

let rec bctx_of_quant cP quant =  
  let rec make = function
    | [] -> cP
    | (x, s)::quant' -> Snoc (make quant', x, s)
  in
  make quant

let rec bctx_of_ctx_exp = function
  | Snoc(g, x, e) -> Snoc(bctx_of_ctx_exp g, x, e)
  | _ -> Nil

let drop_suffix cP n =
  let rec drop cP' n' =
    match cP', n' with
    | _, 0 -> cP'
    | Snoc(cP', _, _), n' -> drop cP' (n'-1)
    | _ -> raise (Error.Error ("Tried to drop " ^ string_of_int n ^ " terms out of " ^ print_bctx cP ^ " which is too short."))
  in
  drop cP n

let keep_suffix cP n =
  let rec keep cP' n' =
    match cP', n' with
    | _, 0 -> Nil
    | Snoc(cP', x, t), n' -> Snoc(keep cP' (n'-1), x, t)
    | _ -> raise (Error.Error ("Tried to keep " ^ string_of_int n ^ " terms out from " ^ print_bctx cP ^ " which is too short."))
  in
  keep cP n

(* Substitution utilities *)

(* let rec wkn_pat_subst_by_n s = *)
(*   let rec shift = function *)
(*     | CShift n -> CShift (n+1) *)
(*     | CEmpty -> CEmpty *)
(*     | CDot (s, n) -> CDot (shift s, n+1) *)
(*   in *)
(*   function *)
(*   | 0 -> s *)
(*   | n -> wkn_pat_subst_by_n (CDot (shift s , 0)) (n-1) *)

(* let rec lookup_pat_subst err i s = match i, s with *)
(*   | 0, CDot (_, j) -> j *)
(*   | i, CDot (s', _) -> lookup_pat_subst err (i-1) s' *)
(*   | i, CShift n -> (i + n) *)
(*   | i, CEmpty -> raise (Error.Error err) *)


(* let rec comp_pat_subst err s s' = *)
(* match s, s' with *)
(* | CShift n, CShift n' -> CShift (n + n') *)
(* | _, CEmpty -> CEmpty *)
(* | CEmpty, CShift _ -> raise (Error.Error err) *)
(* | CEmpty, CDot _ -> raise (Error.Error err) *)
(* | s, CDot(s', x) -> *)
(*    CDot(comp_pat_subst err s s', lookup_pat_subst err x s) *)
(* | CDot (s', x), CShift n -> comp_pat_subst err s' (CShift (n-1)) *)

exception Inv_fail

let apply_inv_pat_subst e s =
  let rec add_id_cdot n s =
    if n = 0 then s
    else CDot(add_id_cdot (n-1) s, (n-1, None))
  in
  let rec apply_inv e s =
    let rec apply_inv' n s cnt =
      match s with
      | CDot (s, m) when n = m -> BVar (cnt, None)
      | CDot (s, _) -> apply_inv' n s (cnt+1)
      | CShift m when fst n < m -> raise Inv_fail
      | CShift m -> BVar (fst n - m, None) (* We lose the projection. Fix plox *)
      | CEmpty -> raise Inv_fail
    in
    match e, s with
    | e, CShift 0 -> e
    | BVar n, _ -> apply_inv' n s 0
    | Star, _ -> Star
    | SPi(tel, t'),_ ->
      SPi(List.map (fun (i,x,e) -> i, x, apply_inv e s) tel, apply_inv t' (add_id_cdot (List.length tel) s))
    | Lam (x, e), _ -> Lam(x, apply_inv e (CDot (s, (0, None))))
    | AppL (e, es), _ -> AppL(apply_inv e s, List.map (fun e -> apply_inv e s) es)
    | SBCtx cP, _ -> SBCtx cP
    | Empty, _ -> Empty
    | Shift n, CShift m when n >= m -> Shift (n - m)
    | Shift n, CShift _ -> raise Inv_fail
    | Shift n, CEmpty -> Empty
    | Shift n, CDot(_,_) -> assert false
    | Dot (s, e), s' -> Dot (apply_inv s s', apply_inv e s')
    | SCtx t, _ -> SCtx t
    | SConst n, _ -> SConst n
    | Unbox(e, s'), _ -> Unbox (e, apply_inv s' s)
    | Block _, _ -> assert false
    | _ -> assert false
  in
  try Some (apply_inv e s)
  with Inv_fail ->
    Debug.print (fun () -> "Cannot find an inverse for " ^ Print.print_pat_subst s ^ " to apply to " ^ print_syn_exp e); 
    None

let apply_inv_subst e s =
  let rec add_id_cdot n s =
    if n = 0 then s
    else Dot(add_id_cdot (n-1) s, BVar (n-1, None))
  in
  let rec apply_inv e s =
    let rec apply_inv' n s cnt =
      match s with
      | Dot (s, BVar m) when n = m -> BVar (cnt, None)
      | Dot (s, _) -> apply_inv' n s (cnt+1)
      | Shift m when fst n < m -> raise Inv_fail
      | Shift m -> BVar (fst n - m, snd n) (* This is suspicious. Please revisit when broken *)
      | Empty -> raise Inv_fail
      | _ -> raise Inv_fail (* Not a substitution *)
    in
    match e, s with
    | e, Shift 0 -> e
    | BVar n, _ -> apply_inv' n s 0
    | Star, _ -> Star
    | SPi(tel, t'),_ ->
      SPi(List.map (fun (i,x,e) -> i, x, apply_inv e s) tel, apply_inv t' (add_id_cdot (List.length tel) s))
    | Lam (xs, e), _ -> Lam(xs, apply_inv e (shiftS_syn  (List.length xs) s))
    | AppL (e, es), _ -> AppL(apply_inv e s, List.map (fun e -> apply_inv e s) es)
    | SBCtx cP, _ -> SBCtx cP
    | Empty, _ -> Empty
    | Shift n, Shift m when n >= m -> Shift (n - m)
    | Shift n, Shift m -> Debug.print (fun () -> "Incompatible shifts " ^ string_of_int n ^ " " ^ string_of_int m)  ; raise Inv_fail
    | Shift n, Empty -> Empty
    | Shift n, Dot(_,_) -> assert false

    | Dot (s, e), s' -> Dot (apply_inv s s', apply_inv e s')
    | SCtx t, _ -> SCtx t
    | SConst n, _ -> SConst n
    | Unbox(e, s'), _ -> Unbox (e, apply_inv s' s)
    | _ -> raise (Error.Violation ("Failed to apply inverse substitution " ^ print_syn_exp s
                                   ^ " because it was not a substitution."))
  in
  try Some (apply_inv e s)
  with Inv_fail -> 
    Debug.print (fun () -> "Cannot find an inverse for " ^ print_syn_exp s ^ " to apply to " ^ print_syn_exp e);
    None

let rec apply_inv_psubst_ctx cP s =
  match s with
  | CEmpty -> Nil
  | CShift n -> drop_suffix cP n
  | CDot(s, e) -> 
    let cP' = apply_inv_psubst_ctx cP s in
    let t = assert false in (* TODO infer the type of e, using the internal type checker that we have to write *)    
    Snoc(cP', Name.gen_string "x", t)

  let rec apply_inv_subst_ctx cP s =
  match s with
  | Empty -> Nil
  | Shift n -> drop_suffix cP n
  | Dot(s, e) -> 
    let cP' = apply_inv_subst_ctx cP s in
    let t = assert false in (* TODO infer the type of e, using the internal type checker that we have to write *)    
    Snoc(cP', Name.gen_string "x", t)
  | _ -> raise (Error.Violation ("Applying inverse substitution where substitution is in fact " ^ (print_syn_exp s)))

let rec psubst_of_pat_subst = function
  | CShift n -> Shift n
  | CEmpty -> Empty
  | CDot (s, i) -> Dot (psubst_of_pat_subst s, BVar i)

(* Produces cP' such that cP |- s : cP' *)
let rec shift_cp_inv_pat_subst cP s =
  match cP, s with
  | _, CEmpty -> Nil
  | _, CShift 0 -> cP
  | Snoc (cP', _, _), CShift n  -> shift_cp_inv_pat_subst cP' (CShift (n-1))
  | cP, CDot (s, i) ->
    let t = lookup_bound cP i in
    match apply_inv_pat_subst t s with
    | Some t' -> Snoc (shift_cp_inv_pat_subst cP s, "_", t')
    | None -> raise (Error.Error "Cannot infer substitution")

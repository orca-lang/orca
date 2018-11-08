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
  | Comp (e1, _, e2)
  | Dot (e1, e2) -> fvs e1 @ fvs e2
  | ShiftS (_, e) -> fvs e
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
  | Comp (e1, cP, e2) -> Comp (f e1, refresh_bctx rep cP, f e2)
  | ShiftS (n, e) -> ShiftS (n, f e)
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
  | Comp (e1, cP, e2) -> Comp (f e1, refresh_free_var_bctx (x, y) cP, f e2)
  | ShiftS (n, e) -> ShiftS (n, f e)
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
  | ShiftS (n, e) -> ShiftS (n, f e)
  | Comp (e1, cP, e2) -> Comp (f e1, subst_bctx (x, es) cP, f e2)
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
let rec weaken_syn n = let f = weaken_syn n in function
| Star -> Star
  | SCtx sch -> SCtx sch 
  | SPi (tel, t) -> assert false
  | Lam (xs, e) -> assert false
  | AppL (e1, es) -> AppL(f e1, List.map f es)
  | SConst n -> SConst n
  | BVar i -> BVar (i + n)
  | Unbox (e, s) -> Unbox(e, f s)
  | Empty -> Empty
  | Shift n' -> Shift (n + n')
  | Dot (s, e) -> Dot (f s, f e)
  | SBCtx cP -> assert false
  | Block cs -> assert false

let rec apply_syn_subst (sigma : syn_exp) : syn_exp -> syn_exp = function
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
  | Unbox (e1, e2) -> Unbox(subst (x, es) e1, f e2)
  | Empty -> Empty
  | Shift n -> Shift n
  | ShiftS (n, e) -> ShiftS (n, f e)
  | Comp (e1, cP, e2) -> Comp (f e1, subst_bctx (x, es) cP, f e2)
  | Dot (e1, e2) -> Dot (f e1, f e2)
  | SBCtx cP -> SBCtx (subst_bctx (x, es) cP)
  | Block cs -> Block (subst_block (x, es) cs)
 
and apply_syn_subst_stel sigma = function
| [] -> [], sigma
| (icit, x, t)::stel -> 
  let el = (icit, x, apply_syn_subst sigma t) in
  let sigma' = Dot (weaken_syn_subst 1 sigma, BVar i0) in
  let stel', sigma'' = apply_syn_subst_stel sigma' stel) in
  el::stel', sigma''

and apply_syn_subst_lam sigma = function
| [] -> [], sigma
| (x, t)::xs -> 
  let el = (icit, x, apply_syn_subst sigma t) in
  let sigma' = Dot (weaken_syn_subst 1 sigma, BVar i0) in
  let xs', sigma'' = apply_syn_subst_lam sigma' xs) in
  el::xs', sigma''

(* generate meta variables for all the quantifiers in a schema and apply them to the block (generates a new block) *)
let mk_quant_subst cP quant block = 
  let rec mk_subst = function
    | [] -> Empty, cP, []
    | (x, t) :: quant -> 
      let x' = Name.gen_name x in
      Debug.print (fun () -> "mk_quant_subst generates new name: " ^ print_name x');
      let sigma, cP', flex = mk_subst quant in
      Dot (sigma, Unbox(Var x', id_sub)), Snoc(cP', x, Clos(t,sigma, cP')), x'::flex
  in
  let sigma, cP', flex = mk_subst quant in
  let rec subst_schema cP' sigma = function
    | [] -> []
    | (x, t) :: block -> 
      Debug.print (fun () -> "subst_schema turns type " ^ print_syn_exp t ^ " into type " ^ print_syn_exp (Clos (t, sigma, cP')));
      (x, Clos (t, sigma, cP')) :: subst_schema (Snoc(cP', x, Clos(t,sigma, cP'))) (Dot(sigma, BVar (0,None))) block
  in
  let block' = subst_schema cP sigma block in
  block', flex

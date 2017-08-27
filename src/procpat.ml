open Name
open Syntax
open Print
open MetaOp
open MetaSub
module A = Syntax.Apx
module I = Syntax.Int
module AP = Print.Apx
module IP = Print.Int
module PP = Pretty

type pat =
  | Apx of A.pat
  | Int of I.pat

type pats = pat list

let rec print_pat (p : pat) : string = match p with
  | Apx p -> AP.print_pat p
  | Int p -> IP.print_pat p
and print_pats ps = String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)

let rec get_domain cP s =
  match cP, s with
  | _, CEmpty -> I.Nil
  | _, CDot(s, y) ->
     I.Snoc(get_domain cP s, "_", lookup_bound cP y)
  | _, CShift 0 -> cP
  | I.Snoc(g, _, _), CShift m -> get_domain g (CShift (m-1))
  | _, CShift m -> raise (Error.Error ("Expected context " ^ IP.print_bctx cP ^ " to have at least "
                                       ^ string_of_int m ^ " variable" ^ if m > 1 then "s" else "" ^ " to shift over."))

let pvar_list_of_ctx : I.ctx -> I.pats = List.map (fun (x, _) -> I.PVar x)

let punbox_list_of_ctx cP : I.ctx -> I.syn_pat list = List.map (fun (x, _) -> I.PUnbox(x, pid_sub, cP))

type single_psubst = name * I.pat
type psubst = single_psubst list

let print_psubst c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ " := " ^ IP.print_pat e) c)) ^ "]"

let rec psubst sign (x, p') = function
  | I.PVar n when n = x -> p'
  | I.PVar n -> I.PVar n
  | I.Inacc e -> I.Inacc (subst (x, I.exp_of_pat p') e)
  | I.PConst (n, ps) -> I.PConst (n, List.map (psubst sign (x, p')) ps)
  | I.PBCtx cP -> I.PBCtx (bctx_psubst sign (x, p') cP)
  | I.PUnder -> I.PUnder
  | I.PTBox (cP, p) -> let cP' = subst_bctx (x, I.exp_of_pat p') cP in
                       I.PTBox (cP', syn_psubst sign cP' (x, p') p)
and syn_psubst sign cP (x, p') = function
  | I.PBVar i -> I.PBVar i
  | I.PPar n when n = x ->
    begin match p' with
    | I.PVar m -> I.PUnbox (m, pid_sub, cP)
    | I.Inacc e -> I.SInacc (e, pid_sub, cP)
    | I.PTBox (cP', q) -> assert false
    | _ -> assert false
    end
  | I.PPar n -> I.PPar n

  | I.PLam (xs, p) -> I.PLam (xs, syn_psubst sign (bctx_of_lam_pars cP xs) (x, p') p) (* What about shifts in p'? *)
  | I.PSConst (n, ps) -> I.PSConst (n, List.map (syn_psubst sign cP (x, p')) ps)
  | I.PUnbox (n, s, cP') when n = x ->
     begin match p' with
       | I.PVar m -> I.PUnbox (m, s, cP')
       | I.Inacc e -> I.SInacc (e, s, cP')
       | I.PTBox (cP'', q) ->  (* cP' should be equal to cP'' *)
          let rec push_unbox (s, cP') = function
            | I.PBVar i ->
               I.PBVar (lookup_pat_subst ("Expected term " ^ IP.print_syn_pat q ^ " to be closed") i s)
            | I.PLam (xs , p) -> I.PLam(xs, push_unbox (wkn_pat_subst_by_n s (List.length xs), bctx_of_lam_pars cP' xs) p)
            | I.PSConst (n,ps) -> I.PSConst (n, List.map (push_unbox (s, cP')) ps)
            | I.PUnbox (m, s', cP'') ->
               I.PUnbox (m, comp_pat_subst ("Mismatching substitution from term " ^ IP.print_syn_pat q) s s', cP'')
            | I.SInacc (e, s', cP'') ->
               I.SInacc (e, comp_pat_subst ("Mismatching substitution from term " ^ IP.print_syn_pat q) s s', cP'')
            | I.PEmpty  -> I.PEmpty
            | I.PShift n ->
               let rec comp s n =
                 match s, n with
                 | _, 0 ->
                    let rec convert = function
                      | CEmpty -> I.PEmpty
                      | CShift n -> I.PShift n
                      | CDot (s, i) -> I.PDot (convert s, I.PBVar i)
                    in
                    convert s
                 | CDot (s', _), _ -> comp s' (n-1)
                 | CShift n', _ -> I.PShift (n+n')
                 | CEmpty, _ -> raise (Error.Error ("Empty substitution applied to a shift."))
               in
               comp s n
            | I.PDot (sigma, p) -> I.PDot (push_unbox (s, cP') sigma, push_unbox (s, cP') p)
            | I.PPar n -> I.PPar n
          in
          push_unbox (s, cP') q
       | _ -> assert false
     end
  | I.PUnbox (n, s, cP) -> I.PUnbox (n, s, cP)
  | I.SInacc (e, s, cP) -> I.SInacc (subst (x, I.exp_of_pat p') e, s, cP)
  | I.PEmpty -> I.PEmpty
  | I.PShift n -> I.PShift n
  | I.PDot (s, p) -> I.PDot (syn_psubst sign cP (x, p') s, syn_psubst sign cP (x, p') p)

and bctx_psubst sign (x, p') = function
  | I.PNil -> I.PNil
  | I.PSnoc (cP, s, t) -> I.PSnoc (bctx_psubst sign (x, p') cP, s, subst_syn (x, I.exp_of_pat p') t)
  | I.PCtxVar n when n = x ->
     begin match p' with
     | I.PBCtx p -> p
     | I.PVar m -> I.PCtxVar m
     | _ -> raise (Error.Violation ("Why not?" ^ IP.print_pat p'))
     end
  | I.PCtxVar n -> I.PCtxVar n

(* let psubst sign (x, p') (p : I.pat) : I.pat = *)
  (* match p with *)
  (* | Apx p -> *)
  (*    let rec sanity_check = function *)
  (*      | A.PPar n when n = x -> raise (Error.Violation ("Pattern substitution done on variable " *)
  (*                                    ^ print_name n ^ " which we believe should have not occured due to linearity")) *)
  (*      | A.PVar n when n = x -> raise (Error.Violation ("Pattern substitution done on variable " *)
  (*                                    ^ print_name n ^ " which we believe should have not occured due to linearity")) *)
  (*      | A.Inacc e -> raise (Error.Violation "Pattern substitution applied to approximate inaccessible pattern") *)
  (*      | A.PLam (xs, p) -> A.PLam (xs, sanity_check p) *)
  (*      | A.PConst (n, ps) -> A.PConst (n, List.map sanity_check ps) *)
  (*      | A.PDot (p1, p2) -> A.PDot (sanity_check p1, sanity_check p2) *)
  (*      | A.PSnoc (p1, s, p2) -> A.PSnoc (sanity_check p1, s, sanity_check p2) *)
  (*      | p -> p *)
  (*    in *)
  (*    Apx (sanity_check p) *)
  (* | Int p -> *)
  (* psubst_int sign (x, p') p *)

let rec compose_single_with_psubst sign s = function
  | [] -> []
  | (y, t') :: sigma -> (y, psubst sign s t') :: (compose_single_with_psubst sign s sigma)

let pats_of_psubst : psubst -> I.pats = List.map (fun (x, p) -> p)

let simul_psubst sign sigma p =
  List.fold_left (fun p s -> psubst sign s p) p sigma

let simul_syn_psubst sign cP sigma p =
  List.fold_left (fun p s -> syn_psubst sign cP s p) p sigma

(* let simul_psubst_int sign sigma p = *)
(*   List.fold_left (fun p s -> psubst_int sign s p) p sigma *)

let simul_psubst_on_list sign sigma ps =
  List.map (simul_psubst sign sigma) ps

let simul_syn_psubst_on_list sign cP sigma ps =
  List.map (simul_syn_psubst sign cP sigma) ps

let compose_psubst sign sigma delta = List.map (fun (x, t) -> x, simul_psubst sign sigma t) delta

let psubst_of_ctx : I.ctx -> psubst = List.map (fun (x, _) -> x, I.PVar x)

let simul_psubst_on_ctx sign sigma =
    List.map (fun (x, e) -> x, simul_psubst sign sigma e)

let rec rename_ctx_using_psubst (cG : I.ctx) (sigma : psubst) =
  match cG with
  | [] -> []
  | (x, t) :: cG' ->
     match lookup_ctx sigma x with
     | Some (I.PVar y) -> (y, t) :: (rename_ctx_using_psubst cG' sigma)
     | _ -> (x, t) :: (rename_ctx_using_psubst cG' sigma)


let shift_psubst_by_ctx sigma cG =
  let sigma' = sigma @ (List.map (fun (x, _) -> x, I.PVar x) cG) in
  Debug.print (fun () -> "Shift called with sigma = " ^ print_psubst sigma
                         ^ "\ncG = " ^ IP.print_ctx cG
                         ^ "\nresulting in " ^ print_psubst sigma'
                         ^ ".");
  sigma'

let rec exp_of_pat_subst : pat_subst -> I.syn_exp = function
  | CShift n -> I.Shift n
  | CEmpty -> I.Empty
  | CDot (s, i) -> I.Dot(exp_of_pat_subst s, I.BVar i)

let exp_of_pat sign cP : pat -> I.exp = function
  | Int p -> I.exp_of_pat p
  | Apx p -> raise (Error.Violation "This is Sparta")

let rec proc_pats : A.pats -> pats = List.map (fun p -> Apx p)

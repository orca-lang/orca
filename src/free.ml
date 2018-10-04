open Syntax.Int 

let rec fv_pat =
  function
  | PVar n -> [n]
  | Inacc _ -> []
  | PConst (n, ps) -> fv_pats ps
  | PBCtx cP -> fv_pat_bctx cP
  | PUnder -> []
  | PTBox (cP, p) -> fv_syn_pat p (* MMMM *)

and fv_syn_pat =
  function
  | PBVar i -> []
  | PPar (n, _) -> [n]
  | PLam (f, p) -> fv_syn_pat p
  | PSConst (n, ps) -> fv_syn_pats ps
  | PUnbox (n, _, _) -> [n]
  | SInacc (_, _, _) -> []
  | PEmpty -> []
  | PShift i -> []
  | PDot (p1, p2) -> fv_syn_pat p1 @ fv_syn_pat p2

and fv_pat_bctx =
  function
  | PNil -> []
  | PSnoc (cP, _, _) -> fv_pat_bctx cP
  | PCtxVar n -> [n]

and fv_pats ps = List.concat(List.map fv_pat ps)
and fv_syn_pats ps = List.concat(List.map fv_syn_pat ps)
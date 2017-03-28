open Syntax.Int
open Print.Int
open Name
open Sign
open Meta

let rec contextify (sign, cG) (g : exp) =
  match Whnf.whnf sign g with
  | Nil -> BNil
  | Var x ->
    begin match lookup_ctx_fail cG x with
    | Ctx -> CtxVar x
    | _ -> raise (Error.Violation ("Tried to contextify non context variable " ^ print_name x))
    end
  | Snoc (g', x, e) ->
    let cP = contextify (sign, cG) g' in
    BSnoc (cP, x, e)
  | _ -> raise (Error.Error ("Expected context, obtained " ^ print_exp g))

let rec decontextify cP =
  match cP with
  | BNil -> Nil
  | CtxVar x -> Var x
  | BSnoc (cP', x, e) -> Snoc (decontextify cP', x, e)

let is_ctx (sign, cG) = function
  | Nil
  | Snoc _ -> true
  | Var g when lookup_ctx_fail cG g = Ctx -> true
  | _ -> false

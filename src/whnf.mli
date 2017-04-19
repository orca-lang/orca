open Sign
open Syntax
open Syntax.Int

val whnf : signature -> exp -> exp
val rewrite : signature -> bctx -> syn_exp -> syn_exp
(* val normalize : signature -> exp -> exp *)

open Sign
open Syntax
open Syntax.Int

val whnf : signature -> exp -> exp
val whnf_open : signature -> bctx -> exp -> exp
val normalize : signature -> exp -> exp
val apply_inv : exp -> pat_subst -> exp option

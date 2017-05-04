open Sign
open Syntax
open Syntax.Int

val whnf : signature -> exp -> exp
val rewrite : signature -> bctx -> syn_exp -> syn_exp
val whnf_ctx : signature -> ctx -> ctx
val whnf_bctx : signature -> bctx -> bctx
val whnf_stel : signature -> bctx -> stel -> stel

val normalize : signature -> exp -> exp
val normalize_syn : signature -> bctx -> syn_exp -> syn_exp
val normalize_bctx : signature -> bctx -> bctx

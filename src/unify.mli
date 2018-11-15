open Sign
open Name
open Meta
open Syntax.Int

val unify : signature * ctx -> exp -> exp -> ctx * subst
val unify_syn : signature * ctx -> bctx -> syn_exp -> syn_exp -> ctx * subst
val unify_many : signature * ctx -> exp list -> exp list -> ctx * subst
val unify_bctx : signature * ctx -> bctx -> bctx -> ctx * subst

val unify_flex : signature * ctx -> name list -> exp -> exp -> ctx * subst
val unify_flex_syn : signature * ctx -> bctx -> name list -> syn_exp -> syn_exp -> ctx * subst
val unify_flex_schemata : signature * ctx -> name list -> schema -> schema -> ctx * subst
val unify_flex_many : signature * ctx -> name list -> exp list -> exp list -> ctx * subst
val unify_flex_many_syn : signature * ctx -> bctx -> name list -> syn_exp list -> syn_exp list -> ctx * subst

type unification_problem
exception Unification_failure of unification_problem
val print_unification_problem : unification_problem -> string

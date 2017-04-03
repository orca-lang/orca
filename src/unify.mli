open Sign
open Name
open Meta
open Syntax.Int

val unify : signature * ctx -> exp -> exp -> ctx * subst
val unify_open : signature * ctx -> bctx -> exp -> exp -> ctx * subst
val unify_many : signature * ctx -> exp list -> exp list -> ctx * subst
val unify_bctx : signature * ctx -> bctx -> bctx -> ctx * subst

val unify_flex : signature * ctx -> name list -> exp -> exp -> ctx * subst
val unify_flex_many : signature * ctx -> name list -> exp list -> exp list -> ctx * subst
val unify_flex_many_open : signature * ctx -> bctx -> name list -> exp list -> exp list -> ctx * subst

type unification_problem
exception Unification_failure of unification_problem
val print_unification_problem : unification_problem -> string

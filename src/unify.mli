open Syntax.Int
open Sign
open Name
open Meta

type unification_problem
val print_unification_problem : unification_problem -> string

exception Unification_failure of unification_problem

(* val occur_check : signature -> Name.name -> exp -> bool *)
(* val occur_check_tel : signature -> Name.name -> tel -> bool *)
(* val occur_check_stel : signature -> Name.name -> stel -> bool *)

val print_subst : (Name.name * exp) list -> string

(* type ctx_weakening = *)
(*     NoWeakeaning *)
(*   | LeftWeakening of int *)
(*   | RightWeakening of int *)

(* val infer_head_type : signature * ctx -> bctx -> exp -> exp *)

(* val unify_flex : signature * ctx -> ctx -> bctx -> name list -> exp -> exp -> exp -> ctx * subst *)
(* val unify_heads : signature * ctx -> ctx -> bctx -> name list -> exp -> exp -> exp list -> exp list -> *)
(*                   ctx * subst *)

val unify_flex_many :
  signature * ctx -> ctx -> bctx -> name list -> exp list -> exp list -> exp list -> ctx * subst

(* val unify_flex_pi : signature * ctx -> ctx -> bctx -> name list -> tel -> exp -> tel -> exp -> *)
(*                     ctx * single_subst list *)

(* val unify_flex_spi : signature * ctx -> ctx -> bctx -> name list -> stel -> exp -> stel -> exp -> *)
                     (* ctx * subst *)

(* val get_flex_vars : ctx -> exp -> exp -> name list *)

val unify : signature * ctx -> exp -> exp -> exp -> ctx * subst

(* val unify_many : signature * ctx -> exp list -> exp list -> exp list -> ctx * subst *)

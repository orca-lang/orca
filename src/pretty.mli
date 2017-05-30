open Format
open Syntax.Int

(* Fomratter pretty printers *)
val fmt_program : formatter -> program -> unit
val fmt_programs : formatter -> program list -> unit
val fmt_exp : ctx -> int -> formatter -> exp -> unit
val fmt_syn_exp : ctx -> bctx -> formatter -> syn_exp -> unit
val fmt_bctx : ctx -> formatter -> bctx -> unit
val fmt_ctx : formatter -> ctx -> unit


(* String pretty printers *)
val print_program : program -> string
val print_programs : program list -> string
val print_exp : ctx -> exp -> string
val print_syn_exp : ctx -> bctx -> syn_exp -> string
val print_bctx : ctx -> bctx -> string
val print_ctx : ctx -> string
val print_stel : ctx -> bctx -> stel -> syn_exp -> string

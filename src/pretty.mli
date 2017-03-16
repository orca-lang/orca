open Format
open Syntax.Int
open Sign

(* Fomratter pretty printers *)
val fmt_program : signature -> formatter -> program -> unit
val fmt_programs : signature -> formatter -> program list -> unit
val fmt_exp : signature * ctx -> bctx -> formatter -> exp -> unit


(* String pretty printers *)
val print_program : signature -> program -> string
val print_programs : signature -> program list -> string
val print_exp : signature * ctx -> bctx -> exp -> string

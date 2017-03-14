open Format
open Syntax.Int
open Sign

(* Fomratter pretty printers *)
val fmt_program : signature -> formatter -> program -> unit
val fmt_exp : signature * ctx -> formatter -> exp -> unit
val fmt_tel_entry : signature * ctx  -> formatter -> tel_entry -> unit
val fmt_tel : signature * ctx  -> formatter -> tel -> unit


(* String pretty printers *)
val print_program : signature -> program -> string
val print_exp : signature * ctx -> exp -> string
val print_tel_entry : signature * ctx -> tel_entry -> string
val print_tel : signature * ctx -> tel -> string

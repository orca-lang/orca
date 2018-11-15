
module Ugly : Ppsig.Pretty_printer = struct

  open Format
  open Syntax.Int
  open Print.Int

  (* String pretty printers *)
  let print_program = print_program
  let print_programs = print_programs
  let print_exp _ = print_exp
  let print_pats _ = print_pats
  let print_syn_exp _ _ = print_syn_exp
  let print_bctx _ = print_bctx
  let print_ctx = print_ctx
  let print_stel _ _ stel e = (print_stel stel) ^ " ->> " ^ (Print.Int.print_syn_exp e)
  let print_tree = print_tree


  (* Fomratter pretty printers *)
  let fmt_program _ p = assert false (* formatter -> program -> unit *)
  let fmt_programs _ _ = assert false (* formatter -> program list -> unit *)
  let fmt_exp _ _ _ _  = assert false (* ctx -> int -> formatter -> exp -> unit *)
  let fmt_pats _ _  _ = assert false (* ctx -> formatter -> pat list -> unit *)
  let fmt_syn_exp _ _ _ = assert false (* ctx -> bctx -> int -> formatter -> syn_exp -> unit *)
  let fmt_bctx _ _ _ = assert false (* ctx -> formatter -> bctx -> unit *)
  let fmt_ctx _ _ = assert false (*: formatter -> ctx -> unit *)
end

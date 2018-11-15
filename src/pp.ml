open Format
open Syntax.Int

open Ppsig
open Ugly
open Pretty

let simple_pp = ref false

let set_simple_pp () = simple_pp := true ; ()

module Pretty : Ppsig.Pretty_printer = struct

  (* String pretty printers *)
  let print_program p = if !simple_pp then Ugly.print_program p else Pretty.print_program p
  let print_programs ps = if !simple_pp then Ugly.print_programs ps else Pretty.print_programs ps
  let print_exp cG = if !simple_pp then Ugly.print_exp cG else Pretty.print_exp cG
  let print_pats cG = if !simple_pp then Ugly.print_pats cG else Pretty.print_pats cG
  let print_syn_exp cG cP = if !simple_pp then Ugly.print_syn_exp cG cP else Pretty.print_syn_exp cG cP
  let print_bctx cG = if !simple_pp then Ugly.print_bctx cG else Pretty.print_bctx cG
  let print_ctx cG = if !simple_pp then Ugly.print_ctx cG else Pretty.print_ctx cG
  let print_stel cG cP stel e = if !simple_pp then Ugly.print_stel cG cP stel e else Pretty.print_stel cG cP stel e
  let print_tree t = if !simple_pp then Ugly.print_tree t else Pretty.print_tree t

  (* Fomratter pretty printers *)
  let fmt_program fmt p = if !simple_pp then assert false else Pretty.fmt_program fmt p (* formatter -> program -> unit *)
  let fmt_programs fmt ps = if !simple_pp then assert false else Pretty.fmt_programs fmt ps (* formatter -> program list -> unit *)
  let fmt_exp cD n fmt e = if !simple_pp then assert false else Pretty.fmt_exp cD n fmt e (* ctx -> int -> formatter -> exp -> unit *)
  let fmt_pats cD fmt ps = if !simple_pp then assert false else Pretty.fmt_pats cD fmt ps (* ctx -> formatter -> pat list -> unit *)
  let fmt_syn_exp = if !simple_pp then assert false else Pretty.fmt_syn_exp (* ctx -> bctx -> int -> formatter -> syn_exp -> unit *)
  let fmt_bctx = if !simple_pp then assert false else Pretty.fmt_bctx (* ctx -> formatter -> bctx -> unit *)
  let fmt_ctx = if !simple_pp then assert false else Pretty.fmt_ctx (*: formatter -> ctx -> unit *)
end

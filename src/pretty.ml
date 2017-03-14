(* Pretty printer - Should produce a nice output *)

open Syntax
open Syntax.Int

(* Supports utf8 and colours that Format doesn't, and the output is
   cute *)
open Fmt

let fmt_program sign pps p =
  Fmt.pf pps "def"

(* The string formatters *)

let produce_string f e =
  let _ = Format.flush_str_formatter () in
  f Format.str_formatter e ;
  Format.flush_str_formatter()

let print_program sign p = produce_string (fmt_program sign) p

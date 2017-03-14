(* Pretty printer - Should produce a nice output *)

open Syntax
open Syntax.Int

(* Supports utf8 and colours that Format doesn't, and the output is
   cute *)
open Fmt

(* Ansi formats *)

let keyword_color = `Magenta
let bound_var_color = `Green
let comp_var_color = `Underline
let def_color = `Blue

(* Formatter pretty printers *)

let keyword = styled keyword_color string (* coloured word *)
let def = styled def_color string
let const = styled def_color

let rec fmt_tel_entry (sign, cG) pps = function
  | Explicit, n, t ->
     Fmt.pf pps "@[( %a : %a)@]"
            Name.fmt_name n
            (fmt_exp (sign, cG)) t
  | Implicit, n, t ->
     Fmt.pf pps "@[{ %a : %a}@]"
            Name.fmt_name n
            (fmt_exp (sign, cG)) t

and fmt_tel (sign, cG) pps = function
  | (Explicit, n, t) :: tel when Name.is_name_floating n ->
     Fmt.pf pps "%a ->"
            (fmt_exp (sign, cG)) t
  | entry :: tel ->
     Fmt.pf pps "%a%a"
            (fmt_tel_entry (sign, cG)) entry
            (fmt_tel (sign, cG)) tel
  | [] -> ()

and fmt_exp (sign, cG) pps = function
  | Const n ->
     Fmt.pf pps "%a"
    (const string) n
  | _ -> Fmt.pf pps "exp"

let fmt_universe pps = function
  | 0 -> Fmt.pf pps "set"
  | n -> Fmt.pf pps "set%d" n

let fmt_program sign pps = function
  | Data (n, [], [], 0, ds) ->
     Fmt.pf pps "@[%a %a %a@]\n"
            keyword "data"
            def n
            keyword "where"

  | Data (n, [], [], u, ds) ->
     Fmt.pf pps "@[%a %a : %a %a@]\n"
            keyword "data"
            def n
            fmt_universe u
            keyword "where"

  | Data (n, ps, is, u, ds) ->
     Fmt.pf pps "@[%a %a %a: %a %a %a@]\n"
            keyword "data"
            def n
            (list (fmt_tel_entry (sign, []))) ps
            (fmt_tel (sign, [])) is
            fmt_universe u
            keyword "where"

  | _ -> ()

(* The string formatters *)

let produce_string f e =
  let _ = Format.flush_str_formatter () in
  f Format.str_formatter e ;
  Format.flush_str_formatter()

let print_program sign p = produce_string (fmt_program sign) p
let print_exp cs e = produce_string (fmt_exp cs) e
let print_tel_entry cs te = produce_string (fmt_tel_entry cs) te
let print_tel cs tel = produce_string (fmt_tel cs) tel

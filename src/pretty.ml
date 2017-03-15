(* Pretty printer - Should produce a nice output *)

open Syntax
open Syntax.Int

(* Supports utf8 and colours that Format doesn't, and the output is
   cute *)
open Fmt

(* Ansi formats *)

let keyword_color = `Magenta
let bound_var_color = `Green
let comp_var_color = `Bold
let def_color = `Blue

(* Non-breakable space *)
let nbsp : unit Fmt.t = fun pps () -> Fmt.pf pps " "

(* Formatter pretty printers *)

let keyword = styled keyword_color string (* coloured word *)
let def = styled def_color string
let const = styled def_color string
let comp_var = styled comp_var_color Name.fmt_name

let rec fmt_tel_entry (sign, cG) pps = function
  | Explicit, n, t ->
     Fmt.pf pps "(%a : %a)"
            comp_var n
            (fmt_exp (sign, cG)) t
  | Implicit, n, t ->
     Fmt.pf pps "{%a : %a}"
            comp_var n
            (fmt_exp (sign, cG)) t

and fmt_tel (sign, cG) pps = function
  | (Explicit, n, t) :: tel when Name.is_name_floating n ->
     Fmt.pf pps "%a"
            (fmt_exp (sign, cG)) t
  | entry :: tel ->
     Fmt.pf pps "%a %a"
            (fmt_tel_entry (sign, cG)) entry
            (fmt_tel (sign, cG)) tel
  | [] -> ()

and fmt_exp (sign, cG) pps = function
  | Set 0 -> (string pps "set")
  | Set n -> ()
  | Const n ->
     Fmt.pf pps "%a"
            const n
  | App(e, es) ->
     Fmt.pf pps "%a %a"
            (fmt_exp (sign, cG)) e
            (list ~sep:nbsp (fmt_exp (sign, cG))) es

  | Var n -> comp_var pps n

  | Hole n ->
     Fmt.pf pps "?%a"
            Name.fmt_name n

  | e -> Fmt.pf pps "¡%s!" (Print.Int.print_exp e)

let rec fmt_pat (sign, cG) pps = function
  | PVar n -> comp_var pps n
  | Innac e ->
     Fmt.pf pps ".%a"
            (fmt_exp (sign, cG)) e
  | PConst (n, pats) ->
     Fmt.pf pps "(%a %a)"
            const n
            (fmt_pats (sign, cG)) pats
  | p -> Fmt.pf pps "¡%s!" (Print.Int.print_pat p)

and fmt_pats (sign, cG) pps pats =
  Fmt.pf pps "%a"
         (list ~sep:nbsp (fmt_pat (sign, cG))) pats


let fmt_universe pps = function
  | 0 -> Fmt.pf pps "set"
  | n -> Fmt.pf pps "set%d" n

let fmt_decl sign pps = function
  | n, [], (tn, es) ->
     Fmt.pf pps "| %a : %a @[%a@]"
            const n
            const tn
            (list ~sep:sp (fmt_exp (sign, []))) es

  | n, tel, (tn, es) ->
     Fmt.pf pps "| %a : %a -> %a @[%a@]"
            const n
            (fmt_tel (sign, [])) tel
            const tn
            (list ~sep:sp (fmt_exp (sign, []))) es

let rec fmt_decls sign pps = function
  | [] -> ()
  | d::ds -> Fmt.pf pps "%a@,%a"
                    (fmt_decl sign) d
                    (fmt_decls sign) ds

let fmt_rhs sign pps = function
  | Just e -> fmt_exp (sign, []) pps e (* should have the context from the patterns *)
  | Impossible n ->
     Fmt.pf pps "impossible %a" comp_var n

let fmt_pat_decl sign pps (pats, rhs) =
  Fmt.pf pps "| %a => %a"
         (fmt_pats (sign, [])) pats
         (fmt_rhs sign) rhs

let rec fmt_pat_decls sign pps = function
  | [] -> ()
  | pat::pats -> Fmt.pf pps "%a@,%a"
                    (fmt_pat_decl sign) pat
                    (fmt_pat_decls sign) pats


let fmt_program sign pps = function
  (* printing inductive types *)
  | Data (n, [], [], 0, ds) ->
     Fmt.pf pps "%a %a %a@,%a@,"
            keyword "data"
            def n
            keyword "where"
            (vbox (fmt_decls sign))
            ds

  | Data (n, [], [], u, ds) ->
     Fmt.pf pps "%a %a : %a %a@,%a@,"
            keyword "data"
            def n
            fmt_universe u
            keyword "where"
            (fmt_decls sign)
            ds

  | Data (n, ps, is, u, ds) ->
     Fmt.pf pps "%a %a %a: %a %a %a@,%a@,"
            keyword "data"
            def n
            (list (fmt_tel_entry (sign, []))) ps
            (fmt_tel (sign, [])) is
            fmt_universe u
            keyword "where"
            (fmt_decls sign)
            ds

  | Def (n, t, e) ->
     Fmt.pf pps "%a %a : %a = %a"
            keyword "def"
            const n
            (fmt_exp (sign, [])) t
            (fmt_exp (sign, [])) e

  | DefPM (n, [], t, pats) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "def"
            const n
            (fmt_exp (sign, [])) t
            keyword "where"
            (fmt_pat_decls sign) pats


  | DefPM (n, tel, t, pats) ->
     Fmt.pf pps "%a %a : %a -> %a %a@,%a"
            keyword "def"
            const n
            (fmt_tel (sign, [])) tel
            (fmt_exp (sign, [])) t
            keyword "where"
            (fmt_pat_decls sign) pats

  | _ -> ()

let fmt_programs sign pps ps =
  let rec fmt_programs sign pps = function
    | [] -> ()
    | p::ps ->
       Fmt.pf pps "%a@,%a"
              (fmt_program sign) p
              (fmt_programs sign) ps
  in
  Fmt.pf pps "%a@."
         (vbox (fmt_programs sign))
         ps

(* The string formatters *)

let produce_string f e =
  let _ = Format.flush_str_formatter () in
  f Format.str_formatter e ;
  Format.flush_str_formatter()

let print_program sign p = produce_string (fmt_program sign) p
let print_programs sign p = produce_string (fmt_programs sign) p
let print_exp cs e = produce_string (fmt_exp cs) e
let print_tel_entry cs te = produce_string (fmt_tel_entry cs) te
let print_tel cs tel = produce_string (fmt_tel cs) tel

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
let comp_var cG pps n =
  match Name.beautify_name n cG with
  | None -> (styled comp_var_color Name.fmt_name) pps n
  | Some s -> (styled comp_var_color string) pps s
let bound_var = styled bound_var_color Fmt.int
let bound_name = styled bound_var_color Fmt.string

(* some dummy type *)
let dt = EmptyS

let rec fmt_tel_entry (sign, cG) pps = function
  | Explicit, n, t ->
     Fmt.pf pps "(%a : %a)"
            (comp_var ((n, dt) ::cG)) n
            (fmt_exp (sign, cG)) t
  | Implicit, n, t ->
     Fmt.pf pps "{%a : %a}"
            (comp_var ((n, dt) ::cG)) n
            (fmt_exp (sign, cG)) t

and fmt_tel (sign, cG) pps (tel, e) =
  match tel with
  | (Explicit, n, t) :: tel when Name.is_name_floating n ->
     Fmt.pf pps "(%a) -> %a"
            (fmt_exp (sign, cG)) t
            (fmt_tel (sign, (n, dt)::cG)) (tel, e)
  | (_, n, _ as entry) :: tel ->
     Fmt.pf pps "%a %a"
            (fmt_tel_entry (sign, cG)) entry
            (fmt_tel (sign, (n, dt)::cG)) (tel, e)
  | [] ->
     Fmt.pf pps "%a"
            (fmt_exp (sign, cG))  e

and fmt_stel_entry (sign, cG) pps = function
  | Explicit, n, t ->
     Fmt.pf pps "(%a : %a)"
            bound_name n
            (fmt_exp (sign, cG)) t
  | Implicit, n, t ->
     Fmt.pf pps "{%a : %a}"
            bound_name n
            (fmt_exp (sign, cG)) t

and fmt_stel (sign, cG) pps = function
  | entry :: tel ->
     Fmt.pf pps "%a %a"
            (fmt_stel_entry (sign, cG)) entry
            (fmt_stel (sign, cG)) tel
  | [] -> ()

and fmt_exp (sign, cG) pps = function
  | Set 0 -> (string pps "set")
  | Set n ->
     Fmt.pf pps "set%d" n
  | Const n ->
     Fmt.pf pps "%a"
            const n
  | App(e, es) ->
     Fmt.pf pps "(%a %a)"
            (fmt_exp (sign, cG)) e
            (list ~sep:nbsp (fmt_exp (sign, cG))) es

  | Var n -> comp_var cG pps n

  | Hole n ->
     Fmt.pf pps "?%a"
            Name.fmt_name n

  | Star -> string pps "*"
  | Ctx -> string pps "ctx"

  | Pi (tel, e) ->
     Fmt.pf pps "%a"
            (fmt_tel (sign, cG)) (tel, e)

  | SPi (stel, e) ->
          Fmt.pf pps "%a ->> %a"
            (fmt_stel (sign, cG)) stel
            (fmt_exp (sign, cG)) e

  | Box (g, e) ->
     Fmt.pf pps "(%a |- %a)"
            (fmt_exp (sign, cG)) g
            (fmt_exp (sign, cG)) e

  | Fn (xs, e) ->
     let cG' = (List.map (fun x -> x, dt) xs) @ cG in
     Fmt.pf pps "fn %a => %a"
            (list ~sep:nbsp (comp_var cG')) xs
            (fmt_exp (sign, cG')) e

  | Comp(e1, e2) ->
     Fmt.pf pps "%a o %a"
            (fmt_exp (sign, cG)) e1
            (fmt_exp (sign, cG)) e2

  | ShiftS e ->
     Fmt.pf pps "⇑%a"
            (fmt_exp (sign, cG)) e

  | Annot (e1, e2) ->
     Fmt.pf pps "%a : %a"
            (fmt_exp (sign, cG)) e1
            (fmt_exp (sign, cG)) e2

  | AppL(e, es) ->
     Fmt.pf pps "(%a ' %a)"
            (fmt_exp (sign, cG)) e
            (list ~sep:nbsp (fmt_exp (sign, cG))) es

  | BVar i ->
     Fmt.pf pps "i%a"
            bound_var i
  | Lam (xs, e) ->
     Fmt.pf pps "\\%a. %a"
            (list bound_name) xs
            (fmt_exp (sign, cG)) e

  | Clos (e1, e2) ->
     Fmt.pf pps "%a[%a]"
            (fmt_exp (sign, cG)) e1
            (fmt_exp (sign, cG)) e2

  | EmptyS -> string pps "^"
  | Shift n ->
     Fmt.pf pps "^%d" n
  | Dot (e1, e2) ->
     Fmt.pf pps "%a; %a"
            (fmt_exp (sign, cG)) e1
            (fmt_exp (sign, cG)) e2

  | Nil -> string pps "0"

  | Snoc (e1, n, e2) ->
     Fmt.pf pps "%a, %s: %a"
            (fmt_exp (sign, cG)) e1
            n
            (fmt_exp (sign, cG)) e2

  | Dest n -> string pps n

let rec fmt_pat_subst pps = function
  | CShift 0 ->
     Fmt.pf pps "id"
  | CShift n ->
     Fmt.pf pps "^%d" n
  | CEmpty -> string pps "^"
  | CDot (sigma, i) ->
     Fmt.pf pps "%a; i%a"
            fmt_pat_subst sigma
            bound_var i


let rec fmt_pat (sign, cG) pps = function
  | PVar n -> comp_var cG pps n
  | Innac e ->
     Fmt.pf pps ".%a"
            (fmt_exp (sign, cG)) e

  | PConst (n, []) ->
     Fmt.pf pps "%a"
            const n
  | PConst (n, pats) ->
     Fmt.pf pps "(%a %a)"
            const n
            (fmt_pats (sign, cG)) pats

  (* syntax *)

  | PBVar i ->
     Fmt.pf pps "i%a"
            bound_var i
  | PLam (xs, p) ->
     Fmt.pf pps "\\%a. %a"
            (list bound_name) xs
            (fmt_pat (sign, cG)) p

  | PClos (n, psub) ->
     Fmt.pf pps "%a[%a]"
            (comp_var cG) n
            fmt_pat_subst psub

  | PEmptyS -> string pps "^"
  | PShift n ->
     Fmt.pf pps "^%d" n
  | PDot (p1, p2) ->
     Fmt.pf pps "%a; %a"
            (fmt_pat (sign, cG)) p1
            (fmt_pat (sign, cG)) p2

  | PNil -> string pps "0"

  | PSnoc (p1, n, p2) ->
     Fmt.pf pps "%a, %s: %a"
            (fmt_pat (sign, cG)) p1
            n
            (fmt_pat (sign, cG)) p2

  | PPar n ->
     Fmt.pf pps "<:%a"
            (comp_var cG) n

  (* extra cases *)
  | PUnder
  | PWildcard -> string pps "¿?"

and fmt_pats (sign, cG) pps pats=
  Fmt.pf pps "%a"
         (list ~sep:nbsp (fmt_pat (sign, cG))) pats



let fmt_universe pps = function
  | 0 -> Fmt.pf pps "set"
  | n -> Fmt.pf pps "set%d" n

let fmt_decl (sign, cG) pps = function
  | n, [], (tn, es) ->
     Fmt.pf pps "| %a : %a @[%a@]"
            const n
            const tn
            (list ~sep:sp (fmt_exp (sign, cG))) es

  | n, tel, (tn, es) ->
     Fmt.pf pps "| %a : %a"
            const n
            (fmt_tel (sign, cG)) (tel, App(Const tn, es))

let rec fmt_decls (sign, cG) pps = function
  | [] -> ()
  | d::ds -> Fmt.pf pps "%a@,%a"
                    (fmt_decl (sign, cG)) d
                    (fmt_decls (sign, cG)) ds

let fmt_rhs (sign, cG) pps = function
  | Just e -> fmt_exp (sign, cG) pps e
  | Impossible n ->
     Fmt.pf pps "impossible %a" (comp_var cG) n

let fmt_pat_decl (sign, cG) pps (pats, rhs) =
  let cG' = (List.map (fun x -> x, dt) (Meta.fv_pats pats)) @ cG in
  Fmt.pf pps "%a => %a"
         (list ~sep:nbsp (fmt_pat (sign, cG'))) pats
         (fmt_rhs (sign, cG')) rhs

let rec fmt_pat_decls (sign, cG) pps = function
  | [] -> ()
  | pat::pats -> Fmt.pf pps "%a@,%a"
                    (fmt_pat_decl (sign, cG)) pat
                    (fmt_pat_decls (sign, cG)) pats


let rec fmt_sdecl sign pps (n, stel, (tn, es)) =
  Fmt.pf pps "| %a : %a @,"
         def n
         (fmt_tel (sign, [])) (stel, App(Const tn, es))


let rec fmt_sdecls sign pps = function
  | [] -> ()
  | d::ds -> Fmt.pf pps "%a@,%a"
                   (fmt_sdecl sign) d
                   (fmt_sdecls sign) ds

let rec fmt_params (sign, cG) pps = function
  | [] -> ()
  | (_,n,_ as p) ::ps ->
     Fmt.pf pps "%a%a"
            (fmt_tel_entry (sign, cG)) p
            (fmt_params (sign, (n, dt):: cG)) ps

let fmt_program sign pps = function
  (* printing inductive types *)
  | Data (n, [], [], 0, ds) ->
     Fmt.pf pps "%a %a %a@,%a@,"
            keyword "data"
            def n
            keyword "where"
            (vbox (fmt_decls (sign, [])))
            ds

  | Data (n, [], [], u, ds) ->
     Fmt.pf pps "%a %a : %a %a@,%a@,"
            keyword "data"
            def n
            fmt_universe u
            keyword "where"
            (fmt_decls (sign,[]))
            ds

  | Data (n, ps, is, u, ds) ->
     let cG = List.map (fun (_, n, _) -> n, dt) ps in
     Fmt.pf pps "%a %a %a: %a %a@,%a@,"
            keyword "data"
            def n
            (fmt_params (sign, [])) ps
            (* (list ~sep:nbsp (fmt_tel_entry (sign, cG))) ps *)
            (fmt_tel (sign, cG)) (is, Set u)
            (* fmt_universe u *)
            keyword "where"
            (fmt_decls (sign, cG))
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
            (fmt_pat_decls (sign, [])) pats


  | DefPM (n, tel, t, pats) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "def"
            const n
            (fmt_tel (sign, [])) (tel, t)
            keyword "where"
            (fmt_pat_decls (sign, [])) pats

  | Syn (n, [], ds) ->
     Fmt.pf pps "%a %a %a@,%a"
            keyword "syn"
            const n
            keyword "where"
            (fmt_sdecls sign) ds

  | Syn (n, tel, ds) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "syn"
            const n
            (fmt_tel (sign, [])) (tel, Star)
            keyword "where"
            (fmt_sdecls sign) ds

  | p -> string pps (Print.Int.print_program p)

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

(* Pretty printer - Should produce a nice output *)

open Name
open Syntax
open Syntax.Int


(* Supports utf8 and colours that Format doesn't, and the output is
   cute *)
open Fmt

(* Beautify variable *)

let rec beautify_bound_name x cP =
  let rec count = function
    | CtxVar _
      | Nil -> 0
    | Snoc (cP', x', _) when x = x' -> 1 + count cP'
    | Snoc (cP', x', _) -> count cP'
  in
  let c = count cP in
  if c = 0 then x
  else x ^ string_of_int c

let rec beautify_bound_names xs cP =
  match xs with
  |[] -> []
  | x::xs ->
    let x' = beautify_bound_name x cP in
    x'::beautify_bound_names xs (Snoc (cP, x, Star)) (* star is a dummy type *)

let rec beautify_idx i cP =
  if not (do_beautify ()) then None
  else match i, cP with
  | _, CtxVar _
  | _, Nil -> None
  | 0, Snoc(cP', x, _) -> Some (beautify_bound_name x cP')
  | i, Snoc(cP', _, _) -> beautify_idx (i-1) cP'

(* This is meant as higher than any other paren level. Raise if needed *)
let never_paren = 20

(* Ansi formats *)

let keyword_color = `Bold
let bound_var_color = `Green
let comp_var_color = `Magenta
let def_color = `Blue

(* Non-breakable space *)
let nbsp : unit Fmt.t = fun pps () -> Fmt.pf pps " "

(* Formatter pretty printers *)

let keyword = styled keyword_color string (* coloured word *)
let def = styled def_color string
let const = styled def_color string

let comp_var, comp_new_var =
  let with_beautify f cG pps n =
    match f n cG with
    | None -> (styled comp_var_color Name.fmt_name) pps n
    | Some s -> (styled comp_var_color string) pps s
  in
  with_beautify Name.beautify_name, with_beautify Name.beautify_new_name

let bound_var = styled bound_var_color Fmt.int
let bound_name = styled `Bold (styled bound_var_color string)

let bound_var_name cG pps i =
  match beautify_idx i cG with
  | None -> bound_var pps i
  | Some s -> bound_name pps s

(* some dummy types *)
let dt = Set 0
let dst = Star

let rec bctx_of_names xs cP =
  match xs with
  | [] -> cP
  | x::xs -> Snoc(bctx_of_names xs cP, x, dst)

let rec fmt_tel_entry cG pps = function
  | Explicit, n, t ->
     Fmt.pf pps "(%a : %a)"
            (comp_var ((n, dt) ::cG)) n
            (fmt_exp cG 2) t
  | Implicit, n, t ->
     Fmt.pf pps "{%a : %a}"
            (comp_var ((n, dt) ::cG)) n
            (fmt_exp cG 2) t

and fmt_tel cG pps (tel, e) =
  let maybe_lparen = function
    | Pi _ -> "("
    | _ -> ""
  in
  let maybe_rparen = function
    | Pi _ -> ")"
    | _ -> ""
  in
  let rec fmt_tel' cG floating pps (tel, e) =
    match tel with
    | (Explicit, n, t) :: tel when Name.is_name_floating n ->
      Fmt.pf pps (if floating then "%s%a%s -> %a" else "-> %s%a%s -> %a")
        (maybe_lparen t)
        (fmt_exp cG 5) t
        (maybe_rparen t)
        (fmt_tel' ((n, dt)::cG) true) (tel, e)
    | (_, n, _ as entry) :: tel ->
      Fmt.pf pps "%a %a"
        (fmt_tel_entry cG) entry
        (fmt_tel' ((n, dt)::cG) false) (tel, e)
    | [] -> Fmt.pf pps (if not floating then "-> %a" else "%a") (fmt_exp cG 5) e
  in
  fmt_tel' cG true pps (tel, e)

and fmt_stel_entry cG cP pps = function
  | Explicit, n, t ->
     Fmt.pf pps "(%a : %a)"
            bound_name n
            (fmt_syn_exp cG cP 3) t
  | Implicit, n, t ->
     Fmt.pf pps "{%a : %a}"
            bound_name n
            (fmt_syn_exp cG cP 3) t

and fmt_stel cG cP pps (tel, e) =
  let rec fmt_stel' cG cP floating pps (tel, e) =
    match tel with
    | (Explicit, "_", t) :: tel ->
      Fmt.pf pps (if floating then "%a ->> %a" else "->> %a ->> %a")
        (fmt_syn_exp cG cP 5) t
        (fmt_stel' cG (Snoc(cP, "_", dst)) true) (tel, e)
    | (_, n, t) as se :: tel ->
      Fmt.pf pps "%a %a"
        (fmt_stel_entry cG cP) se
        (fmt_stel' cG (Snoc(cP, n, dst)) false) (tel, e)
    | [] -> Fmt.pf pps (if not floating then "->> %a" else "%a") (fmt_syn_exp cG cP 6) e
  in
  fmt_stel' cG cP true pps (tel, e)

and fmt_exp cG parens pps e =
  let open_paren p = if parens < p then "(" else "" in
  let close_paren p = if parens < p then ")" else "" in
  match e with
  | Set 0 -> Fmt.pf pps "set"
  | Set n ->
    Fmt.pf pps "set%d" n
  | Const n ->
     Fmt.pf pps "%a"
            const n
  | App(e, es) ->
    Fmt.pf pps "%s%a %a%s"
      (open_paren 1)
      (fmt_exp cG 1) e
      (list ~sep:nbsp (fmt_exp cG 0)) es
      (close_paren 1)

  | Var n -> comp_var cG pps n

  | Hole n ->
     Fmt.pf pps "?%a"
            Name.fmt_name n

  | Ctx -> string pps "ctx"

  | Pi (tel, e) ->
    Fmt.pf pps "%s%a%s"
      (open_paren 5)
      (fmt_tel cG) (tel, e)
      (close_paren 5)

  | Box (cP, e) ->
    Fmt.pf pps "%s%a |- %a%s"
      (open_paren 3)
      (fmt_bctx cG) cP
      (fmt_syn_exp cG cP 6) e
      (close_paren 3)

  | TermBox (cP, e) ->
     Fmt.pf pps "%a"
            (fmt_syn_exp cG cP parens) e

     (* Fmt.pf pps "(%a :> %a)" *)
     (*        (fmt_bctx cG) cP *)
     (*        (fmt_syn_exp cG cP) e *)

  | Fn (xs, e) ->
     let cG' = (List.map (fun x -> x, dt) xs) @ cG in
     Fmt.pf pps "%sfn %a => %a%s"
       (open_paren 4)
       (list ~sep:nbsp (comp_var cG')) xs
       (fmt_exp cG' 4) e
       (close_paren 4)

  | Annot (e1, e2) ->
    Fmt.pf pps "%s%a : %a%s"
      (open_paren 2)
      (fmt_exp cG 2) e1
      (fmt_exp cG 2) e2
      (close_paren 2)

  | Dest n -> string pps n

  | BCtx cP -> fmt_bctx cG pps cP

and fmt_syn_exp cG cP parens pps e =
  let open_paren p = if parens < p then "(" else "" in
  let close_paren p = if parens < p then ")" else "" in
  match e with
  | Star -> string pps "*"
  | SCtx -> string pps "ctx"

  | SBCtx cP -> fmt_bctx cG pps cP

  | SPi (stel, e) -> Fmt.pf pps "%s%a%s"
    (open_paren 6)
    (fmt_stel cG cP) (stel, e)
    (close_paren 6)

  (* | Clos (e1, Shift 0, cP') -> *)
  (*   fmt_syn_exp cG cP' pps e1 *)

  | Clos (e1, e2, cP') ->
     Fmt.pf pps "%a[%a]"
            (fmt_syn_exp cG cP' 0) e1
            (fmt_syn_exp cG cP never_paren) e2

  (* | Unbox (e1, Shift 0, _) -> *)
  (*   fmt_exp cG pps e1 *)

  | Unbox (e1, e2, _) ->
     Fmt.pf pps "%a[%a]"
            (fmt_exp cG 0) e1
            (fmt_syn_exp cG cP never_paren) e2

  | Comp(e1, _, e2) ->
    Fmt.pf pps "%s%a o %a%s"
      (open_paren 4)
      (fmt_syn_exp cG cP 4) e1
      (fmt_syn_exp cG cP 3) e2
      (close_paren 4)

  | ShiftS (n, e) ->
     Fmt.pf pps "%s ⇑%d %a%s"
       (open_paren 1)
       n
       (fmt_syn_exp cG cP 1) e
       (close_paren 1)

  | SConst n ->
     Fmt.pf pps "%a"
            const n

  | AppL(e, es) ->
    Fmt.pf pps "%s%a ' %a%s"
      (open_paren 2)
      (fmt_syn_exp cG cP 2) e
      (list ~sep:nbsp (fmt_syn_exp cG cP 1)) es
      (close_paren 2)

  | BVar i ->
     begin match beautify_idx i cP with
     | None -> Fmt.pf pps "i%a"
                      bound_var i
     | Some n -> bound_name pps n
     end
  | Lam (xs, e) ->
     let xs' = List.map fst xs in
     let cP' = bctx_of_names xs' cP in
     Fmt.pf pps "%s\\%a. %a%s"
       (open_paren 5)
       (list bound_name) (beautify_bound_names xs' cP')
       (fmt_syn_exp cG cP' 5) e
       (close_paren 5)

  | Empty -> string pps "^"
  | Shift n ->
     Fmt.pf pps "^%d" n
  | Dot (e1, e2) ->
    Fmt.pf pps "%s%a; %a%s"
      (open_paren 3)
      (fmt_syn_exp cG cP 3) e1
      (fmt_syn_exp cG cP 2) e2
      (close_paren 3)

and fmt_bctx cG pps = function
  | Nil -> string pps "0"
  | Snoc (cP, n, e) ->
    Fmt.pf pps "%a, %a : %a"
           (fmt_bctx cG) cP
           bound_name (beautify_bound_name n cP)
           (fmt_syn_exp cG cP 3) e
  | CtxVar n -> comp_var cG pps n

let rec fmt_ctx pps = function
  | [] -> string pps "."
  | (x, t)::cG ->
     Fmt.pf pps "%a; %a : %a"
            fmt_ctx cG
            (comp_new_var cG) x
            (fmt_exp cG 2) t

let rec fmt_pat_subst pps = function
  | CShift 0 ->
     Fmt.pf pps "^0"
  | CShift n ->
     Fmt.pf pps "^%d" n
  | CEmpty -> string pps "^"
  | CDot (sigma, i) ->
     Fmt.pf pps "%a; i%a"
            fmt_pat_subst sigma
            bound_var i

let rec fmt_pat cG pps = function
  | PVar n -> comp_var cG pps n
  | PPar n ->
     Fmt.pf pps "<:%a"
            (comp_var cG) n
  | Inacc e ->
     Fmt.pf pps ".%a"
            (fmt_exp cG 0) e

  | PConst (n, []) ->
     Fmt.pf pps "%a"
            const n
  | PConst (n, pats) ->
     Fmt.pf pps "(%a %a)"
            const n
            (fmt_pats cG) pats
  | PBCtx(cP) -> fmt_syn_pat_bctx cG pps cP
  | PUnder -> string pps "_"
  | PTBox(cP, p) ->
     fmt_syn_pat cG cP pps p

and fmt_syn_pat_bctx cG pps = function
  | PNil -> string pps "0"
  | PCtxVar n -> comp_var cG pps n
  | PSnoc (cP', n, t) ->
     Fmt.pf pps "%a, %a: %a"
            (fmt_syn_pat_bctx cG) cP'
            bound_name n
            (fmt_syn_exp cG (bctx_of_pat_ctx cP') 3) t

and fmt_syn_pat cG cP pps = function
  | PBVar i ->
    begin match beautify_idx i cP with
    | None -> Fmt.pf pps "i%a"
      bound_var i
    | Some n -> bound_name pps n
    end
  | PLam (xs, p) ->
     let xs' = List.map fst xs in
     let cP' = bctx_of_names xs' cP in
     Fmt.pf pps "(\\%a. %a)"
            (list bound_name) (beautify_bound_names xs' cP)
            (fmt_syn_pat cG cP') p

  | PUnbox (n, CShift 0, _) ->
    comp_var cG pps n

  | PUnbox (n, psub, _) ->
    Fmt.pf pps "%a[%a]"
            (comp_var cG) n
            fmt_pat_subst psub

  | SInacc (e, CShift 0, _) ->
    Fmt.pf pps ".%a"
      (fmt_exp cG 0) e

  | SInacc (e, psub, _) ->
     Fmt.pf pps ".%a[%a]"
            (fmt_exp cG 0) e
            fmt_pat_subst psub

  | PEmpty -> string pps "^"
  | PShift n ->
     Fmt.pf pps "^%d" n
  | PDot (p1, p2) ->
     Fmt.pf pps "%a; %a"
            (fmt_syn_pat cG cP) p1
            (fmt_syn_pat cG cP) p2

  | PSConst (n, []) ->
     Fmt.pf pps "%a"
            const n
  | PSConst (n, pats) ->
     Fmt.pf pps "(%a %a)"
            const n
            (fmt_syn_pats cG cP) pats

and fmt_pats cG pps pats =
  Fmt.pf pps "%a"
         (list ~sep:nbsp (fmt_pat cG)) pats

and fmt_syn_pats cG cP pps pats =
  Fmt.pf pps "%a"
         (list ~sep:nbsp (fmt_syn_pat cG cP)) pats

let fmt_universe pps = function
  | 0 -> Fmt.pf pps "set"
  | n -> Fmt.pf pps "set%d" n

let fmt_decl cG pps = function
  | n, [], (tn, es) ->
     Fmt.pf pps "| %a : %a @[%a@]"
            const n
            const tn
            (list ~sep:sp (fmt_exp cG 0)) es

  | n, tel, (tn, es) ->
     Fmt.pf pps "| %a : %a"
            const n
            (fmt_tel cG) (tel, if es = [] then Const tn else App(Const tn, es))

let rec fmt_decls cG pps = function
  | [] -> ()
  | d::ds -> Fmt.pf pps "%a@,%a"
                    (fmt_decl cG) d
                    (fmt_decls cG) ds

let fmt_rhs cG pps = function
  | Just e -> fmt_exp cG never_paren pps e
  | Impossible n ->
     Fmt.pf pps "impossible %a" (comp_var cG) n

let fmt_pat_decl cG pps (pats, rhs) =
  let cG' = (List.map (fun x -> x, dt) (Meta.fv_pats pats)) @ cG in
  Fmt.pf pps "| %a => %a"
         (list ~sep:nbsp (fmt_pat cG')) pats
         (fmt_rhs cG') rhs

let rec fmt_pat_decls cG pps = function
  | [] -> ()
  | pat::pats -> Fmt.pf pps "%a@,%a"
                    (fmt_pat_decl cG) pat
                    (fmt_pat_decls cG) pats


let rec fmt_sdecl pps (n, stel, (tn, es)) =
  match es with
  | [] ->
    Fmt.pf pps "| %a : %a"
      def n
      (fmt_stel [] Nil) (stel, SConst tn)
  | _ ->
    Fmt.pf pps "| %a : %a"
      def n
      (fmt_stel [] Nil) (stel, AppL(SConst tn, es))


let rec fmt_sdecls pps = function
  | [] -> ()
  | d::ds -> Fmt.pf pps "%a@,%a"
                   fmt_sdecl d
                   fmt_sdecls ds

let rec fmt_params cG pps = function
  | [] -> ()
  | (_,n,_ as p) ::ps ->
     Fmt.pf pps "%a%a"
            (fmt_tel_entry cG) p
            (fmt_params ((n, dt):: cG)) ps

let fmt_program pps = function
  (* printing inductive types *)
  | Data (n, [], [], 0, ds) ->
     Fmt.pf pps "%a %a %a@,%a"
            keyword "data"
            def n
            keyword "where"
            (vbox (fmt_decls []))
            ds

  | Data (n, [], [], u, ds) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "data"
            def n
            fmt_universe u
            keyword "where"
            (fmt_decls [])
            ds

  | Data (n, ps, is, u, ds) ->
     let cG = List.map (fun (_, n, _) -> n, dt) ps in
     Fmt.pf pps "%a %a %a: %a %a@,%a"
            keyword "data"
            def n
            (fmt_params []) ps
            (fmt_tel cG) (is, Set u)
            keyword "where"
            (fmt_decls cG)
            ds
  (* printing definitions and theorems *)
  | Def (n, t, e) ->
     Fmt.pf pps "%a %a : %a = %a"
            keyword "def"
            const n
            (fmt_exp [] never_paren) t
            (fmt_exp [] never_paren) e

  | DefPM (n, [], t, pats) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "def"
            const n
            (fmt_exp [] never_paren) t
            keyword "where"
            (fmt_pat_decls []) pats

  | DefPM (n, tel, t, pats) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "def"
            const n
            (fmt_tel []) (tel, t)
            keyword "where"
            (fmt_pat_decls []) pats

  (* printing specification types *)
  | Syn (n, [], ds) ->
     Fmt.pf pps "%a %a %a@,%a"
            keyword "syn"
            const n
            keyword "where"
            fmt_sdecls ds

  | Syn (n, tel, ds) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "syn"
            const n
            (fmt_stel [] Nil) (tel, Star)
            keyword "where"
            fmt_sdecls ds

  | p -> string pps (Print.Int.print_program p)

let fmt_programs pps ps =
  let rec fmt_programs pps = function
    | [] -> ()
    | p::ps ->
       Fmt.pf pps "%a@,%a"
              fmt_program p
              fmt_programs ps
  in
  Fmt.pf pps "%a@."
         (vbox fmt_programs)
         ps

(* The string formatters *)

let produce_string f e =
  let _ = Format.flush_str_formatter () in
  f Format.str_formatter e ;
  Format.flush_str_formatter()

let print_program p = produce_string fmt_program p
let print_programs p = produce_string fmt_programs p
let print_exp cG e = produce_string (fmt_exp cG never_paren) e
let print_bctx cG cP = produce_string (fmt_bctx cG) cP
let print_ctx cP = produce_string fmt_ctx cP
let print_syn_exp cG cP e = produce_string (fmt_syn_exp cG cP never_paren) e
let print_tel_entry cG te = produce_string (fmt_tel_entry cG) te
let print_tel cG tel = produce_string (fmt_tel cG) tel
let print_stel_entry cG cP te = produce_string (fmt_stel_entry cG cP) te
let print_stel cG cP tel t = produce_string (fmt_stel cG cP) (tel, t)

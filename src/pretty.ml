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

let rec beautify_idx (n, proj) cP =
  if not (do_beautify ()) then None
  else match n, cP with
  | _, CtxVar _
  | _, Nil -> None
  | 0, Snoc(cP', x, _) -> Some (beautify_bound_name x cP')
  | i, Snoc(cP', _, _) -> beautify_idx (n-1, proj) cP'

(* This is meant as higher than any other paren level. Raise if needed *)
let never_paren = 20

(* Ansi formats *)

let keyword_color = `Bold
let bound_var_color = `Green
let comp_var_color = `Magenta
let def_color = `Blue

(* Non-breakable space *)
let nbsp : unit Fmt.t = fun pps () -> Fmt.pf pps " "
let sapp : unit Fmt.t = fun pps () -> Fmt.pf pps " ' "

(* Formatter pretty printers *)

let keyword = styled keyword_color string (* coloured word *)
let def = styled def_color string
let const = styled def_color string

(* Precedence values *)
let prec_else = 0
let prec_app = 1
let prec_box = 2
let prec_pi = 3
let prec_fun = 4
let prec_annot = 5

let comp_var, comp_new_var =
  let with_beautify f cG pps n =
    match f n cG with
    | None -> (styled comp_var_color Name.fmt_name) pps n
    | Some s -> (styled comp_var_color string) pps s
  in
  with_beautify Name.beautify_name, with_beautify Name.beautify_new_name

let bound_var pps i =
  let bv = function
    | (i, None) -> Fmt.pf pps "%d" i
    | (i, Some j) -> Fmt.pf pps "%d.%d" i j
  in
  (* styled bound_var_color *) (bv i) (* TODO pretty colours? *)

let bound_name = styled `Bold (styled bound_var_color string)

let bound_var_name cG pps i =
  match beautify_idx i cG with
  | None -> bound_var pps i
  | Some s -> bound_name pps s (* TODO print the projection? *)

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

(* parens is an integer computing precedence of enclosing expression.
   If expression has lower precedence (higher number), parentheses are
   added. Current values are
   1 - Application
   2 - Box
   3 - Pi type
   4 - Function
   5 - Annotation
   Note that term box are not being pretty printed so number passed
   to fmt_syn_exp is simply incremented by one (so applications match in
   precedence). This might need to be revised.
*)
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
      (open_paren prec_app)
      (fmt_exp cG prec_app) e
      (list ~sep:nbsp (fmt_exp cG prec_else)) es
      (close_paren prec_app)

  | Var n -> comp_var cG pps n

  | Hole n ->
     Fmt.pf pps "?%a"
            Name.fmt_name n

  | Ctx sch ->
     Fmt.pf pps "ctx %a"
            (fmt_schema cG prec_app) sch

  | Pi (tel, e) ->
    Fmt.pf pps "%s%a%s"
      (open_paren prec_pi)
      (fmt_tel cG) (tel, e)
      (close_paren prec_pi)

  | Box (cP, e) ->
    Fmt.pf pps "%s%a |- %a%s"
      (open_paren prec_box)
      (fmt_bctx cG) cP
      (fmt_syn_exp cG cP 6) e
      (close_paren prec_box)

  | TermBox (cP, e) ->
     Fmt.pf pps "%a"
            (fmt_syn_exp cG cP (parens+1)) e

     (* Fmt.pf pps "(%a :> %a)" *)
     (*        (fmt_bctx cG) cP *)
     (*        (fmt_syn_exp cG cP) e *)

  | Fn (xs, e) ->
     let cG' = (List.map (fun x -> x, dt) xs) @ cG in
     Fmt.pf pps "%sfn %a => %a%s"
       (open_paren prec_fun)
       (list ~sep:nbsp (comp_var cG')) xs
       (fmt_exp cG' prec_fun) e
       (close_paren prec_fun)

  | Annot (e1, e2) ->
    Fmt.pf pps "%s%a : %a%s"
      (open_paren prec_annot)
      (fmt_exp cG prec_annot) e1
      (fmt_exp cG prec_annot) e2
      (close_paren prec_annot)

  | BCtx cP -> Fmt.pf pps "%s%a%s"
    (open_paren 2)
    (fmt_bctx cG) cP
    (close_paren 2)

(* parens is an integer computing precedence of enclosing expression.
   If expression has lower precedence (higher number), parentheses
   are added. Current values are
   1 - ShiftS
   2 - Application
   3 - Dot
   4 - Composition
   5 - Lam
   6 - Spi
   Closures use parentheses unless term is atomic
*)
and fmt_syn_exp cG cP parens pps e =
  let open_paren p = if parens < p then "(" else "" in
  let close_paren p = if parens < p then ")" else "" in
  match e with
  | Star -> string pps "*"
  | SCtx sch ->
     Fmt.pf pps "ctx %a"
            (fmt_schema cG 1) sch

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
      (list ~sep:sapp (fmt_syn_exp cG cP 1)) es
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
  | Block bs ->
     Fmt.pf pps "|%a|" (fmt_block cG cP parens) bs

and fmt_block cG cP parens pps = function
  | [] -> ()
  | (x, t)::[] -> Fmt.pf pps "%s : %a" x (fmt_syn_exp cG cP parens) t
  | (x, t)::bs -> Fmt.pf pps "%s : %a, %a" x (fmt_syn_exp cG cP parens) t (fmt_block cG cP parens) bs

and fmt_schema cG parens pps = function
  |  (Schema ([], ex)) ->
       Fmt.pf pps "%a"
              (fmt_schema_part cG Nil parens) ex

  |  (Schema (im, ex)) ->
      let cP = MetaOp.part_to_bctx im in
       Fmt.pf pps "{%a} %a"
              (fmt_schema_part cG Nil parens) im
              (fmt_schema_part cG cP parens) ex


and fmt_schema_part cG cP parens pps = function
  | [] -> ()
  | [(n, t)] ->
     Fmt.pf pps "%s : %a"
            n
            (fmt_syn_exp cG cP parens) t

  | (n, t)::ps' ->
     Fmt.pf pps "%s : %a, %a"
            n
            (fmt_syn_exp cG cP parens) t
            (fmt_schema_part cG (Snoc (cP, n, t)) parens) ps'

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
  | PPar n ->
    Fmt.pf pps "<:%a"
      (comp_var cG) n

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

let fmt_codecl cG pps = function
  | n, tel, (m, tn, es), e ->
     Fmt.pf pps "| %a : %a"
            const n
            (fmt_tel cG) (tel @ [Explicit, m, if es = [] then Const tn else App(Const tn, es)], e)

let rec fmt_codecls cG pps = function
  | [] -> ()
  | d::ds -> Fmt.pf pps "%a@,%a"
                    (fmt_codecl cG) d
                    (fmt_codecls cG) ds

let fmt_rhs cG pps = function
  | Just e -> fmt_exp cG never_paren pps e
  | Impossible n ->
     Fmt.pf pps "impossible %a" (comp_var cG) n

let fmt_pat_decl cG pps (pats, rhs) =
  let cG' = (List.map (fun x -> x, dt) (MetaOp.fv_pats pats)) @ cG in
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
     Fmt.pf pps "%a %a"
            (fmt_tel_entry cG) p
            (fmt_params ((n, dt):: cG)) ps

let rec fmt_defpm key pps = function
  | (n, [], t, pats) :: def ->
    Fmt.pf pps "%a %a : %a %a@,%a@,%a"
            keyword key
            const n
            (fmt_exp [] never_paren) t
            keyword "where"
            (fmt_pat_decls []) pats
            (fmt_defpm "and") def
  | (n, tel, t, pats) :: def ->
      Fmt.pf pps "%a %a : %a %a@,%a@,%a"
            keyword "def"
            const n
            (fmt_tel []) (tel, t)
            keyword "where"
           (fmt_pat_decls []) pats
           (fmt_defpm "and") def
  | [] -> ()

let rec ind sep = function
  | 0 -> ""
  | n -> sep ^ ind sep (n - 1)

let rec fmt_tree dep pps = function
  | Node (cG, pats, t, n, trs) ->
     Fmt.pf pps "%s* pats: [%a] split on %a : %a@\n%a"
            (ind "  " dep)
            (fmt_pats cG) pats
            (comp_var cG) n
            (fmt_exp cG never_paren) t
            (fmt_trees (dep+1)) trs


  | Incomplete (cG, pats, e) ->
     Fmt.pf pps "%s|-> %a <-- Incomplete"
            (ind "  " dep)
            (fmt_pats cG) pats

  | Leaf (cG, pats, _t, Just body) ->
     Fmt.pf pps "%s|-> %a => %a"
            (ind "  " dep)
            (fmt_pats cG) pats
            (fmt_exp cG 1) body

  | Leaf (cG, pats, e, Impossible n) ->
     Fmt.pf pps "%s|-> impossible: %a"
            (ind "  " dep)
            (comp_var cG) n

and fmt_trees dep pps = function
  | tr :: trs ->
     Fmt.pf pps "%a@\n%a"
            (fmt_tree dep) tr
            (fmt_trees dep) trs
  | [] -> ()


let rec fmt_defpm_tree key pps = function
  | (n, t, tr) :: def ->
      Fmt.pf pps "%a %a : %a %a@\n%a@\n%a"
            keyword "def"
            const n
            (fmt_exp [] never_paren) t
            keyword "where"
           (fmt_tree 0) tr
           (fmt_defpm_tree "and") def
  | [] -> ()

let rec fmt_spec key pps = function
  | (n, [], ds) :: def ->
    Fmt.pf pps "%a %a %a@,%a@,%a"
      keyword key
      const n
      keyword "where"
      fmt_sdecls ds
      (fmt_spec "and") def
  | (n, tel, ds) :: def ->
    Fmt.pf pps "%a %a : %a %a@,%a@,%a"
      keyword key
      const n
      (fmt_stel [] Nil) (tel, Star)
      keyword "where"
      fmt_sdecls ds
      (fmt_spec "and") def
  | [] -> ()

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

  | Codata (n, [], [], 0, ds) ->
     Fmt.pf pps "%a %a %a@,%a"
            keyword "codata"
            def n
            keyword "where"
            (vbox (fmt_codecls []))
            ds

  | Codata (n, [], [], u, ds) ->
     Fmt.pf pps "%a %a : %a %a@,%a"
            keyword "codata"
            def n
            fmt_universe u
            keyword "where"
            (fmt_codecls [])
            ds

  | Codata (n, ps, is, u, ds) ->
     let cG = List.map (fun (_, n, _) -> n, dt) ps in
     Fmt.pf pps "%a %a %a: %a %a@,%a"
            keyword "codata"
            def n
            (fmt_params []) ps
            (fmt_tel cG) (is, Set u)
            keyword "where"
            (fmt_codecls cG)
            ds


  (* printing definitions and theorems *)
  | Def (n, t, e) ->
     Fmt.pf pps "%a %a : %a = %a"
            keyword "def"
            const n
            (fmt_exp [] never_paren) t
            (fmt_exp [] never_paren) e


  | DefPM def -> fmt_defpm "def" pps def

  (* printing specification types *)
  | Spec spec -> fmt_spec "spec" pps spec

  | DefPMTree defs ->
     fmt_defpm_tree "def" pps defs

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
let print_tree tr = produce_string (fmt_tree 0) tr

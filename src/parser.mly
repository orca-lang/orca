%{

open Syntax
open Syntax.Ext
open Rlist

%}

%token DATA CODATA SPEC AND DEF MID AMP RARR COLON SEMICOLON WHERE EQ UNDERSCORE PATTERNWILD CTX
%token LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE LTRIANG RTRIANG
%token FN LAM APPL
%token STAR ARR SARR TURNSTILE TTS (* term turnstile *) STT
%token <int>SET
%token <string>IDENT
%token <string option>HOLE
%token EOF
%token COMMA EMPTYS DOT NIL
%token <int>INDEX
%token <int>SHIFT
%token <int>PROJ

%nonassoc DOT
%left COMMA SEMICOLON
%nonassoc TTS
%nonassoc COLON

%start <Syntax.Ext.program list>program

%{

let unwrap_or def = function
  | None -> def
  | Some x -> x
%}

%%

located(X):
  x = X
  { Loc.make $startpos $endpos x }

program:
| d = toplevel* EOF {d}

toplevel:
| DATA s = IDENT p = params t = type_dec? WHERE option(MID) d = separated_list (MID, decl)
    {Data (s, p, unwrap_or (Loc.ghost (Set 0)) t, d)}
| CODATA s = IDENT p = params t = type_dec? WHERE option (AMP) d = separated_list (AMP, decl)
    {Codata (s, p, unwrap_or (Loc.ghost (Set 0)) t, d)}
| SPEC s = separated_nonempty_list(AND, spec)
    {Spec s}
| DEF d = separated_nonempty_list(AND, def) {DefPM d}
| DEF f = IDENT COLON t = exp EQ e = exp {Def (f, t, e)}

spec:
| s = IDENT t = type_dec? WHERE option(MID) d = separated_list (MID, decl) {(s, unwrap_or (Loc.ghost Star) t, d)}

def:
| f = IDENT COLON t = exp WHERE option(MID) d = separated_list (MID, def_decl) {(f, t, d)}

type_dec:
| COLON t = exp { t }

params:
| LPAREN s = IDENT+ COLON t = exp_level2 RPAREN p = params {List.map (fun x -> (Explicit, x, t)) s @ p}
| LCURLY s = IDENT+ COLON t = exp_level2 RCURLY p = params {List.map (fun x -> (Implicit, x, t)) s @ p}
| (* empty *) {[]}

decl:
| s = IDENT COLON t = exp {s, t}

def_decl:
| p = simple_pattern+ RARR e = exp {p, e}

exp:
| e = exp_level1 {e}

exp_level1:
| e = located(raw_exp_level1) {e}

raw_exp_level1:
| e1 = exp_level2 COLON e2 = exp_level2 {Annot(e1, e2)}
| e = raw_exp_level2 {e}

exp_level2:
| e = located(raw_exp_level2) {e}

raw_exp_level2:
| FN xs = IDENT+ RARR e = exp_level2 {Fn (xs, e)}
| LAM x = IDENT+ DOT e = exp_level2 {Lam (x, e)}
| e = raw_exp_level3 {e}

exp_level3:
| e = located(raw_exp_level3) {e}

raw_exp_level3:
| s = exp_level4 ARR t = exp_level3 {Arr (s, t)}
| s = exp_level4 SARR t = exp_level3 {SArr (s, t)}
| e = raw_exp_level4 {e}

exp_level4:
| e = located(raw_exp_level4) {e}

raw_exp_level4:
| g = exp_level5 TURNSTILE e = exp_level5 {Box (g, e)}
| TURNSTILE e = exp_level5 {Box (Loc.ghost Nil, e)}
| g = exp_level5 TTS e = exp_level5 {ABox (g, e)}
| CTX sch=schema {Ctx sch}
| e = raw_exp_level5 {e}

exp_level5:
| e = located(raw_exp_level5) {e}

raw_exp_level5:
| s = exp_level5 COMMA b = block {Comma (s, b)}
| s = exp_level5 SEMICOLON e = block {Semicolon (s, e)}
| e = raw_exp_level6 {e}

block:
| b = located(raw_block) {b}

raw_block:
| MID ex=separated_nonempty_list(COMMA, schema_ex) MID { Block (from_list (List.rev ex)) }
| e = raw_exp_level6 {e}

exp_level6:
| e = located(raw_exp_level6) {e}

raw_exp_level6:
        | e1 = exp_level6 e2 = exp_level7 {App (e1, e2)}
| e1 = exp_level6 APPL e2 = exp_level7 {AppL (e1, e2)}
| e = raw_exp_level7 {e}

exp_level7:
| e = located(raw_exp_level7) {e}

raw_exp_level7:
| e1 = exp_level7 LSQUARE e2 = exp RSQUARE {Clos(e1, e2)}
| e = raw_simple_exp {e}

simple_exp:
| e = located(raw_simple_exp) {e}

raw_simple_exp:
| LPAREN t = raw_exp_level1 RPAREN {t}
| STAR {Star}
| n = SET {Set n}
| s = HOLE {Hole s }
| s = IDENT {Ident s}
| EMPTYS {Empty}
| n = SHIFT {Shift n}
| n = INDEX {BVar n}
| NIL {Nil}

schema:
| e = simple_exp {Schema ([], ["_anon", e])}
| LTRIANG quant=separated_nonempty_list(COMMA, schema_ex) RTRIANG e = simple_exp {Schema (quant, ["_anon", e])}
| LTRIANG quant=separated_nonempty_list(COMMA, schema_ex) RTRIANG LSQUARE block=separated_nonempty_list(COMMA, schema_ex) RSQUARE {Schema (quant,block)}
| LSQUARE block=separated_nonempty_list(COMMA, schema_ex) RSQUARE {Schema ([],block)}

schema_ex:
| x=IDENT COLON e=exp_level6 {x,e} 
| e = exp_level6 {"_anon", e}

simple_pattern:
| x = IDENT {PIdent x}
| DOT e = simple_exp {Inacc e}
| LPAREN p = pattern RPAREN {p}
| EMPTYS {PEmpty}
| n = SHIFT {PShift n}
| NIL {PNil}
| UNDERSCORE {PUnder}
| x = IDENT LSQUARE e = exp RSQUARE {PClos (x, e)}
| PATTERNWILD  {PWildcard}

pattern:
| LAM x = IDENT+ DOT p = pattern {PLam (x, p)}
| c = IDENT ps = simple_pattern+ {PConst (c, ps)}
| p1 = pattern SEMICOLON p2 = pattern {PDot (p1, p2)}
| s = pattern COMMA MID e=separated_nonempty_list(COMMA, schema_pat) MID {PCommaBlock (s, e)}
| s = pattern COMMA e = pattern {PComma (s, None, e)}
| s = pattern COMMA x = IDENT COLON e = pattern {PComma (s, Some x, e)}
| p1 = pattern TTS p2 = pattern {PBox (p1, p2)}
| STT x = IDENT pr = PROJ? {PPar (x, pr)}
| p = simple_pattern {p}

schema_pat:
| x = IDENT {x}

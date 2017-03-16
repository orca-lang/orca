%{

open Syntax
open Syntax.Ext

%}

%token DATA CODATA SYN DEF MID AMP RARR COLON SEMICOLON WHERE EQ UNDERSCORE PATTERNWILD CTX
%token LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE
%token FN LAM APPL
%token STAR ARR SARR TURNSTILE TTS (* term turnstile *) STT
%token <int>SET
%token <string>IDENT
%token <string option>HOLE
%token EOF
%token COMMA EMPTYS DOT NIL
%token <int>SHIFT

%nonassoc TURNSTILE TTS
%nonassoc DOT RARR
%left COMMA SEMICOLON
%nonassoc COLON
%right ARR SARR
%left APPL

%nonassoc STAR SHIFT SET EMPTYS IDENT NIL HOLE CTX
%right LPAREN

%start <Syntax.Ext.program list>program

%{

let unwrap_or def = function
  | None -> def
  | Some x -> x
%}

%%

located(X):
  x = X
  { Location.make $startpos $endpos x }

program:
| d = toplevel* EOF {d}

toplevel:
| DATA s = IDENT p = params t = type_dec? WHERE option(MID) d = separated_list (MID, decl)
    {Data (s, p, unwrap_or (Location.ghost (Set 0)) t, d)}
| CODATA s = IDENT p = params t = type_dec? WHERE option (AMP) d = separated_list (AMP, decl)
    {Codata (s, p, unwrap_or (Location.ghost (Set 0)) t, d)}
| SYN s = IDENT t = type_dec? WHERE option(MID) d = separated_list (MID, decl)
    {Syn (s, unwrap_or (Location.ghost Star) t, d)}
| DEF f = IDENT COLON t = exp WHERE option(MID) d = separated_list (MID, def_decl) {DefPM (f, t, d)}
| DEF f = IDENT COLON t = exp EQ e = exp {Def (f, t, e)}

type_dec:
| COLON t = exp { t }

params:
| LPAREN s = IDENT+ COLON t = exp RPAREN p = params {List.map (fun x -> (Explicit, x, t)) s @ p}
| LCURLY s = IDENT+ COLON t = exp RCURLY p = params {List.map (fun x -> (Implicit, x, t)) s @ p}
| (* empty *) {[]}

decl:
| s = IDENT COLON t = exp {s, t}

def_decl:
| p = simple_pattern+ RARR e = exp {p, e}

exp:
| e = located(raw_exp) {e}
| e = almost_simple_exp {e}

raw_exp:
| g = exp TURNSTILE e = exp {Box (g, e)}
| TURNSTILE e = exp {Box (Location.ghost Nil, e)}
| g = IDENT+ TTS e = exp {TBox (g, e)}
| e1 = exp e2 = almost_simple_exp {App (e1, e2)}
| e1 = exp APPL e2 = exp {AppL (e1, e2)}
| e1 = exp COLON e2 = exp {Annot (e1, e2)}
| FN xs = IDENT+ RARR e = exp {Fn (xs, e)}
| LAM x = IDENT+ DOT e = exp {Lam (x, e)}
| s = exp ARR t = exp {Arr (s, t)}
| s = exp SARR t = exp {SArr (s, t)}
| s = exp COMMA e = exp {Comma (s, e)}
| s = exp SEMICOLON e = exp {Semicolon (s, e)}

almost_simple_exp:
| e = simple_exp {e}
| e = located(raw_almost_simple_exp) {e}

raw_almost_simple_exp:
| e1 = almost_simple_exp LSQUARE e2 = exp RSQUARE {Clos (e1, e2)}

simple_exp:
| LPAREN t = exp RPAREN {t}
| e = located(raw_simple_exp) {e}

raw_simple_exp:
| STAR {Star}
| n = SET {Set n}
| s = HOLE { Hole s }
| s = IDENT {Ident s}
| EMPTYS {EmptyS}
| n = SHIFT {Shift n}
| NIL {Nil}
| CTX {Ctx}

simple_pattern:
| x = IDENT {PIdent x}
| DOT e = simple_exp {Innac e}
| LPAREN p = pattern RPAREN {p}
| EMPTYS {PEmptyS}
| n = SHIFT {PShift n}
| NIL {PNil}
| UNDERSCORE {PUnder}
| x = IDENT LSQUARE e = exp RSQUARE {PClos (x, e)}
| PATTERNWILD  {PWildcard}

pattern:
| LAM x = IDENT+ DOT p = pattern {PLam (x, p)}
| c = IDENT ps = simple_pattern+ {PConst (c, ps)}
| p1 = pattern SEMICOLON p2 = pattern {PDot (p1, p2)}
| s = pattern COMMA e = pattern {PComma (s, e)}
| p1 = pattern TTS p2 = pattern {PBox (p1, p2)}
| STT x = IDENT {PPar x}
| p = simple_pattern {p}

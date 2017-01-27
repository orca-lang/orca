%{

open Syntax

%}

%token DATA SYN DEF MID RARR COLON WHERE EQ
%token LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE
%token FN LAM APPL APP
%token STAR ARR TURNSTILE
%token <int>SET
%token <string>IDENT
%token EOF
%token COMMA EMPTYS DOT
%token <int>SHIFT

%right LAM FN
%nonassoc DOT RARR
%right ARR
%left COMMA
%left APPL APP

%nonassoc STAR SHIFT SET EMPTYS IDENT
%right LPAREN LSQUARE

%start <Syntax.program list>program

%%

program:
| d = toplevel* EOF {d}

toplevel:
| DATA s = IDENT p = params COLON t = texp WHERE option(MID) d = separated_list (MID, decl) {Data (s, p, t, d)}
| SYN s = IDENT p = params COLON t = texp WHERE option(MID) d = separated_list (MID, decl) {Syn (s, p, t, d)}
| DEF f = IDENT COLON t = texp WHERE option(MID) d = separated_list (MID, def_decl) {DefPM (f, t, d)}
| DEF f = IDENT COLON t = texp EQ e = texp {Def (f, t, e)}

params:
| LPAREN s = IDENT+ COLON t = texp RPAREN p = params {List.map (fun x -> (Explicit, x, t)) s @ p}
| LCURLY s = IDENT+ COLON t = texp RCURLY p = params {List.map (fun x -> (Implicit, x, t)) s @ p}
| (* empty *) {[]}

decl:
| s = IDENT COLON t = texp {s, t}

def_decl:
| p = pattern+ RARR e = texp {p, e}

ctx:
| x = IDENT COLON e = ctx_exp {[x,e]}
| g = ctx COMMA x = IDENT COLON e = ctx_exp {(x,e)::g}
| {[]}

ctx_exp:
| e1 = ctx_exp e2 = ctx_exp {App (e1, e2)} %prec APP
| e1 = ctx_exp APPL e2 = ctx_exp {AppL (e1, e2)}
| FN x = IDENT RARR e = ctx_exp {Fn (x, e)}
| LAM x = IDENT DOT e = ctx_exp {Lam (x, e)}
| s = ctx_exp ARR t = ctx_exp {Pi ("", s, t)}
| LPAREN t = exp RPAREN {t}
| STAR {Star}
| n = SET {Set n}
| n = SHIFT {Shift n}
| EMPTYS {EmptyS}
| s = IDENT {Ident s}
| e1 = ctx_exp LSQUARE e2 = exp RSQUARE {Clos (e1, e2)}

texp:
| g = ctx TURNSTILE e = exp {Box (g, e)}
| e = exp {e}

exp:
| e1 = exp e2 = exp {App (e1, e2)} %prec APP
| e1 = exp APPL e2 = exp {AppL (e1, e2)}
| FN x = IDENT RARR e = exp {Fn (x, e)}
| LAM x = IDENT DOT e = exp {Lam (x, e)}
| s = exp ARR t = exp {Pi ("", s, t)}
| LPAREN t = texp RPAREN {t}
| STAR {Star}
| n = SET {Set n}
| n = SHIFT {Shift n}
| EMPTYS {EmptyS}
| s = IDENT {Ident s}
| e1 = exp COMMA e2 = exp {Comma (e1, e2)}
| e1 = exp LSQUARE e2 = texp RSQUARE {Clos (e1, e2)}

pattern:
| s = IDENT {s}

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
%nonassoc DOT RARR COLON
%right ARR
%left COMMA
%left APPL APP

%nonassoc STAR SHIFT SET EMPTYS IDENT
%right LPAREN
%left LSQUARE

%start <Syntax.program list>program

%%

program:
| d = toplevel* EOF {d}

toplevel:
| DATA s = IDENT p = params COLON t = bexp WHERE option(MID) d = separated_list (MID, decl) {Data (s, p, t, d)}
| SYN s = IDENT p = params COLON t = bexp WHERE option(MID) d = separated_list (MID, decl) {Syn (s, p, t, d)}
| DEF f = IDENT COLON t = bexp WHERE option(MID) d = separated_list (MID, def_decl) {DefPM (f, t, d)}
| DEF f = IDENT COLON t = bexp EQ e = bexp {Def (f, t, e)}

params:
| LPAREN s = IDENT+ COLON t = bexp RPAREN p = params {List.map (fun x -> (Explicit, x, t)) s @ p}
| LCURLY s = IDENT+ COLON t = bexp RCURLY p = params {List.map (fun x -> (Implicit, x, t)) s @ p}
| (* empty *) {[]}

decl:
| s = IDENT COLON t = bexp {s, t}

def_decl:
| p = pattern+ RARR e = bexp {p, e}

ctx:
| x = IDENT COLON e = ctx_exp {[x,e]}
| g = ctx COMMA x = IDENT COLON e = ctx_exp {(x,e)::g}
| {[]}

ctx_exp:
| e1 = ctx_exp e2 = simple_exp {App (e1, e2)} %prec APP
| e1 = ctx_exp APPL e2 = simple_exp {AppL (e1, e2)}
| FN x = IDENT RARR e = ctx_exp {Fn (x, e)}
| LAM x = IDENT DOT e = ctx_exp {Lam (x, e)}
| s = ctx_exp ARR t = ctx_exp {Pi ("_", s, t)}
| e = simple_exp {e}

bexp:
| g = ctx TURNSTILE e = exp {Box (g, e)}
| g = ctx TURNSTILE h = ctx {CtxBox (g, h)}
| e = exp {e}

exp:
| e1 = exp e2 = comma_exp {App (e1, e2)} %prec APP
| e1 = exp APPL e2 = comma_exp {AppL (e1, e2)}
| FN x = IDENT RARR e = exp {Fn (x, e)}
| LAM x = IDENT DOT e = exp {Lam (x, e)}
| s = exp ARR t = exp {Pi ("_", s, t)}
| e = comma_exp {e}

comma_exp:
| s = comma_exp COMMA e = simple_exp {Comma (s, e)}
| e = simple_exp {e}
    
simple_exp:
| LPAREN t = bexp RPAREN {t}
| STAR {Star}
| n = SET {Set n}
| s = IDENT {Ident s}
| EMPTYS {EmptyS}
| n = SHIFT {Shift n}
| e1 = simple_exp LSQUARE e2 = bexp RSQUARE {Clos (e1, e2)}


pattern:
| s = IDENT {s}

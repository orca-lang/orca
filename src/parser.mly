%{

open Syntax

%}

%token DATA SYN DEF MID RARR COLON WHERE EQ
%token LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE
%token FN LAM APPL
%token STAR ARR TURNSTILE
%token <int>SET
%token <string>IDENT
%token EOF
%token COMMA EMPTYS DOT NIL
%token <int>SHIFT

%nonassoc TURNSTILE
%nonassoc DOT RARR
%left COMMA
%nonassoc COLON
%right ARR
%left APPL

%nonassoc STAR SHIFT SET EMPTYS IDENT NIL
%right LPAREN

%start <Syntax.program list>program

%%

program:
| d = toplevel* EOF {d}

toplevel:
| DATA s = IDENT p = params COLON t = exp WHERE option(MID) d = separated_list (MID, decl) {Data (s, p, t, d)}
| SYN s = IDENT p = params COLON t = exp WHERE option(MID) d = separated_list (MID, decl) {Syn (s, p, t, d)}
| DEF f = IDENT COLON t = exp WHERE option(MID) d = separated_list (MID, def_decl) {DefPM (f, t, d)}
| DEF f = IDENT COLON t = exp EQ e = exp {Def (f, t, e)}

params:
| LPAREN s = IDENT+ COLON t = exp RPAREN p = params {List.map (fun x -> (Explicit, x, t)) s @ p}
| LCURLY s = IDENT+ COLON t = exp RCURLY p = params {List.map (fun x -> (Implicit, x, t)) s @ p}
| (* empty *) {[]}

decl:
| s = IDENT COLON t = exp {s, t}

def_decl:
| p = pattern+ RARR e = exp {p, e}

exp:
| g = exp TURNSTILE e = exp {Box (g, e)}
| e1 = exp e2 = simple_exp {App (e1, e2)}
| e1 = exp APPL e2 = exp {AppL (e1, e2)}
| e1 = exp COLON e2 = exp {Annot (e1, e2)}
| FN x = IDENT RARR e = exp {Fn (x, e)}
| LAM x = IDENT DOT e = exp {Lam (x, e)}
| s = exp ARR t = exp {Pi ("_", s, t)}
| s = exp COMMA e = exp {Comma (s, e)}
| e = simple_exp {e}
    
simple_exp:
| LPAREN t = exp RPAREN {t}
| STAR {Star}
| n = SET {Set n}
| s = IDENT {Ident s}
| EMPTYS {EmptyS}
| n = SHIFT {Shift n}
| NIL {Nil}
| e1 = simple_exp LSQUARE e2 = exp RSQUARE {Clos (e1, e2)}


pattern:
| s = IDENT {s}

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
%left APPL APP
%left COMMA
%nonassoc STAR SHIFT SET EMPTYS IDENT
%right LPAREN LSQUARE

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
| LPAREN s = IDENT+ COLON t = exp RPAREN p = params {List.map (fun x -> ParamE (x, t)) s @ p}
| LCURLY s = IDENT+ COLON t = exp RCURLY p = params {List.map (fun x -> ParamI (x, t)) s @ p}
| (* empty *) {[]}

decl:
| s = IDENT COLON t = exp {s, t}

def_decl:
| p = pattern+ RARR e = exp {p, e}
    
exp:
| e1 = exp e2 = exp {App (e1, e2)} %prec APP
| e1 = exp APPL e2 = exp {AppL (e1, e2)}
| FN x = IDENT RARR e = exp {Fn (x, e)}
| LAM x = IDENT DOT e = exp {Lam (x, e)}
| s = exp ARR t = exp {Pi ("", s, t)}
| LPAREN t = exp RPAREN {t}
| STAR {Star}
| n = SET {Set n}
| n = SHIFT {Shift n}
| EMPTYS {EmptyS}
| s = IDENT {Ident s}
| e1 = exp LSQUARE e2 = exp RSQUARE {Clos (e1, e2)}
    
(* exp: *)
(* | e = simple_exp+ { match e with [m] -> m | m :: ms -> App (m, ms) | _ -> assert false }  *)
(* | FN x = IDENT RARR e = exp { Fn (x, e) } *)
(* | LAM x = IDENT RARR e = exp { Lam (x, e) } *)

(* simple_exp: *)
(* | LPAREN e = exp RPAREN *)
(* | x = IDENT *)
(* | e = simple_exp LSQUARE e = exp RSQUARE *)
(* | ID *)
(* | SHIFT (\* do we want index applied? If so just a numeral? *\) *)

pattern:
| s = IDENT {s}    

%{

open Syntax

%}

%token DATA SYN DEF MID RARR COLON WHERE EQ
%token LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE
%token FN LAM APP 
%token STAR ARR TURNSTILE
%token <int>SET
%token <string>IDENT
%token EOF
%token COMMA ID SHIFT

%right ARR
%right APP
%left COMMA

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
| STAR {Star}
| n = SET {Set n}
(* | s = tp ARR t = tp *)
(* | s = IDENT es = exp* *)
(* | g = context TURNSTILE t = tp *)
(* | LPAREN t = tp RPAREN *)

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

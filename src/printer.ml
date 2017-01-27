open Syntax

let rec print_exp = function
  | Star -> "*"
  | Set n -> "set" ^ string_of_int n
  | Pi (n, t, e) -> "(pi " ^ n ^ " " ^ print_exp t ^ " " ^ print_exp e ^ ")"
  | Box (ctx, e) -> "(|- " ^ print_ctx ctx ^ " " ^ print_exp e ^ ")"
  | Fn (f, e) -> "(fn " ^ f ^ " " ^ print_exp e ^ ")"
  | Lam (f, e) -> "(\ " ^ f ^ " " ^ print_exp e ^ ")"
  | App (e1, e2) -> "(app " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | AppL (e1, e2) -> "(appl " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | Ident n -> n
  | Clos (e1, e2) -> "(clos " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | EmptyS -> "^"
  | Shift n -> "^" ^ string_of_int n
  | Comma (e1, e2) -> "(dot " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

and print_ctx = function
  | Nil -> "."
  | Cons (c, e) -> "(cons " ^ print_ctx c ^ " " ^ print_exp e ^ ")"

let print_decls decls = String.concat "\n" (List.map (fun (n, e) -> "(" ^ n ^ " " ^ print_exp e ^ ")") decls )
let print_pats pats = String.concat " " pats
let print_def_decls decls = String.concat "\n" (List.map (fun (pats, e) -> "(" ^ print_pats pats ^ " " ^ print_exp e ^ ")") decls)

let print_param = function
  | Implicit, n, e -> "(:i " ^ n ^ " " ^ print_exp e ^ ")"
  | Explicit, n, e -> "(:e " ^ n ^ " " ^ print_exp e ^ ")"

let print_params ps = String.concat " " (List.map print_param ps)

let print_program = function
  | Data (n, ps, e, decls) -> "(data " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
  | Syn (n, ps, e, decls) -> "(syn " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
  | DefPM (n, e, decls) -> "(def " ^ n ^ " " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
  | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

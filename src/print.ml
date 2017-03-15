(* This is the basic printer for the AST, it looks bad but it is
   always available without contexts *)
open Syntax

module Ext = struct
  open Syntax.Ext

  let rec print_exp e =
    match Location.content e with
    | Star -> "*"
    | Set n -> "set" ^ string_of_int n
    | Arr (t, e) -> "(-> " ^ print_exp t ^ " " ^ print_exp e ^ ")"
    | SArr (t, e) -> "(->> " ^ print_exp t ^ " " ^ print_exp e ^ ")"
    | Box (ctx, e) -> "(|- " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | TBox (ctx, e) -> "(:> " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | Fn (fs, e) ->
       "(fn " ^ (String.concat " " fs) ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\ " ^ String.concat " " f ^ " " ^ print_exp e ^ ")"
    | App (e1, e2) -> "(" ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | AppL (e1, e2) -> "(' " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Ident n -> n
    | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | EmptyS -> "^"
    | Shift n -> "^" ^ string_of_int n
    | Comma (e1, e2) -> "(, " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Semicolon (e1, e2) -> "(; " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Hole (Some s) -> "?" ^ s
    | Hole None -> "?"
    | Ctx -> "ctx"

  let rec print_pat (p : pat) : string = match p with
    | PBVar i -> "i " ^ string_of_int i
    | PVar n -> N.print_name n
    | PPar' n -> N.print_name n
    | PIdent n -> n
    | Innac e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ String.concat " " f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PClos (n, e) -> "([] " ^ n ^ " " ^ print_exp e ^ ")"
    | PClos' (n, e) -> "([] " ^ N.print_name n ^ " " ^ print_exp e ^ ")"
    | PBox (p1, p2) -> "(:> " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PEmptyS -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PDot (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PComma (p1, p2) -> "(, " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PPar x -> "(<:" ^ x ^ ")"
    | PUnder -> "_"
    | PWildcard -> "._"


  let print_decls decls = String.concat "\n" (List.map (fun (n, e) -> "(" ^ n ^ " " ^ print_exp e ^ ")") decls)
  let print_pats pats = String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") pats)
  let print_def_decls decls = String.concat "\n" (List.map (fun (pats, e) -> "(" ^ print_pats pats ^ " " ^ print_exp e ^ ")") decls)

  let print_param = function
    | Implicit, n, e -> "(:i " ^ n ^ " " ^ print_exp e ^ ")"
    | Explicit, n, e -> "(:e " ^ n ^ " " ^ print_exp e ^ ")"

  let print_params ps = String.concat " " (List.map print_param ps)

  let print_program = function
    | Data (n, ps, e, decls) -> "(data " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | Codata (n, ps, e, decls) -> "(data " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | Syn (n, e, decls) -> "(syn " ^ n ^ " " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | DefPM (n, e, decls) -> "(def " ^ n ^ " " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

end

module Int = struct
  open Syntax.Int
  open Name

  (* Pretty printer -- could be prettier *)
  let print_universe = string_of_int

  let rec print_exp = function
    | Set n -> print_universe n
    | Star -> "*"
    | Ctx -> "ctx"
    | Pi (tel, t) -> print_pi tel t
    | SPi (tel, t) -> print_spi tel t
    | Box (ctx, e) -> "(" ^ print_exp ctx ^ " |- " ^ print_exp e ^ ")"
    | Fn (fs, e) -> "(fn " ^ (String.concat " " (List.map print_name fs)) ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\\ " ^ String.concat " " f ^ " " ^ print_exp e ^ ")"
    | App (e, es) -> "(" ^ print_exp e ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    | AppL (e1, es) -> "(" ^ print_exp e1 ^ " ' " ^ String.concat " ' " (List.map print_exp es) ^ ")"
    | Const n -> n
    | Dest n -> n
    | Var n -> Name.print_name n
    | BVar i -> "i" ^ string_of_int i
    | Clos (e1, e2) -> "(" ^ print_exp e1 ^ " [" ^ print_exp e2 ^ "])"
    | EmptyS -> "^"
    | Shift n -> "^" ^ string_of_int n
    | ShiftS e -> "(^^ " ^ print_exp e ^ ")"
    | Comp (e1, e2) -> "(" ^ print_exp e1 ^ " o " ^ print_exp e2 ^ ")"
    | Dot (e1, e2) -> "(" ^ print_exp e1 ^ " ; " ^ print_exp e2 ^ ")"
    | Snoc (e1, x, e2) -> "(" ^ print_exp e1 ^ ", " ^ x ^ " : " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(" ^ print_exp e1 ^ " : " ^ print_exp e2 ^ ")"
    | Hole s -> "?" ^ print_name s
  and print_pi tel t = match tel with
    | [] -> print_exp t
    | (_, x, e) :: tel when is_name_floating x ->
       "(" ^ print_exp e ^ " -> " ^ print_pi tel t ^ ")"
    | (_, x, e) :: tel -> "(" ^ print_name x ^ " : " ^ print_exp e ^ ") -> " ^ print_pi tel t ^ ")"
  and print_spi tel t = match tel with
    | [] -> print_exp t
    | (_, x, e) :: tel -> "(" ^ x ^ " : " ^ print_exp e ^ ")->> " ^ print_spi tel t ^ ")"

  let print_exps es = "(" ^ String.concat ", " (List.map print_exp es) ^ ")"

  let rec print_pat_subst : pat_subst -> string =
    function
    | CShift n -> "^" ^ string_of_int n
    | CEmpty -> "^"
    | CDot (s, i) -> "(" ^ print_pat_subst s ^ "; i" ^ string_of_int i ^ ")"

  let rec print_pat (p : pat) : string = match p with
    | PVar n -> print_name n
    | PPar n -> "(<: " ^ print_name n ^ ")"
    | PBVar i -> "i" ^ string_of_int i
    | Innac e -> "." ^ print_exp e
    | PLam (f, p) -> "(\ " ^ String.concat " " f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PClos (n, s) -> print_name n ^ "[" ^ print_pat_subst s ^ "]"
    | PEmptyS -> "^"
    | PShift i -> "^ " ^ string_of_int i
    | PDot (p1, p2) -> "(" ^ print_pat p1 ^ " ; " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PSnoc (p1, x, p2) -> "(" ^ print_pat p1 ^ " , " ^ x ^ ":" ^ print_pat p1 ^ ")"
    | PUnder -> "_"
    | PWildcard -> "._"

  let print_tel (tel : tel) : string =
    String.concat ", " (List.map (fun (_, x, e) -> "(" ^ print_name x
                                                   ^ ", " ^ print_exp e ^ ")") tel)

  let print_stel (tel : stel) : string =
    String.concat ", " (List.map (fun (_, x, e) -> "(" ^ x ^ ", " ^ print_exp e ^ ")") tel)

  let print_dsig ((d, es) : dsig) = "(" ^ d ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"

  let print_decls (decls : decls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig) -> "(" ^ n ^ " " ^ print_tel tel
                                                   ^ " " ^ print_dsig dsig ^ ")") decls)

  let print_codecls (decls : codecls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig, e) -> "(" ^ n ^ " " ^ print_tel tel
                    ^ " " ^ print_dsig dsig ^ " " ^ print_exp e ^ ")") decls)


  let print_sdecls (decls : sdecls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig) -> "(" ^ n ^ " " ^ print_stel tel
                                                   ^ " " ^ print_dsig dsig ^ ")") decls)

  let print_pats pats = "(" ^ String.concat " ; "
                                            (List.map (fun p -> "" ^ print_pat p ^ "") pats)
                        ^ ")"

  let print_rhs = function
    | Just e -> print_exp e
    | Impossible x -> "(impossible " ^ print_name x ^ ")"

  let print_def_decls decls =
    String.concat "\n" (List.map (fun (pats, rhs) -> "(" ^ print_pats pats ^ " => " ^ print_rhs rhs ^ ")") decls)

  let print_param = function
    | Implicit, n, e -> "(:i " ^ print_name n ^ " " ^ print_exp e ^ ")"
    | Explicit, n, e -> "(:e " ^ print_name n ^ " " ^ print_exp e ^ ")"

  let print_params ps = String.concat " " (List.map print_param ps)

  let print_subst c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ " := " ^ print_exp e) c)) ^ "]"
  let print_psubst c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ " := " ^ print_pat e) c)) ^ "]"

  let print_program = function
    | Data (n, ps, is, u, decls) ->
      "(data " ^ n ^ " (" ^ print_params ps ^ ") (" ^ print_params is ^ ") " ^ print_universe u  ^ "\n" ^ print_decls decls ^ ")"
    | Codata (n, ps, is, u, decls) ->
       "(data " ^ n ^ " (" ^ print_params ps ^ ") (" ^ print_params is ^ ") " ^ print_universe u  ^ "\n" ^ print_codecls decls ^ ")"

    | Syn (n, tel, decls) -> "(syn " ^ n ^ " " ^ print_tel tel ^ "\n" ^ print_decls decls ^ ")"
    | DefPM (n, tel, e, decls) -> "(def " ^ n ^ " (" ^ print_tel tel ^ ") " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  end

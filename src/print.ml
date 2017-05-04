(* This is the basic printer for the AST, it looks bad but it is
   always available without contexts *)
open Syntax

let rec print_pat_subst : pat_subst -> string =
  function
  | CShift n -> "^" ^ string_of_int n
  | CEmpty -> "^"
  | CDot (s, i) -> "(" ^ print_pat_subst s ^ "; i" ^ string_of_int i ^ ")"


module Ext = struct
  open Syntax.Ext

  let rec print_exp e =
    match Location.content e with
    | Star -> "*"
    | Set n -> "set" ^ string_of_int n
    | Arr (t, e) -> "(" ^ print_exp t ^ " -> " ^ print_exp e ^ ")"
    | SArr (t, e) -> "(" ^ print_exp t ^ " ->> " ^ print_exp e ^ ")"
    | Box (ctx, e) -> "(" ^ print_exp ctx ^ " |- " ^ print_exp e ^ ")"
    | ABox (e1, e2) -> "(" ^ print_exp e1 ^ " :> " ^ print_exp e2 ^ ")"
    | Fn (fs, e) ->
       "(fn " ^ (String.concat " " fs) ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\ " ^ String.concat " " f ^ " " ^ print_exp e ^ ")"
    | App (e1, e2) -> "(" ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | AppL (e1, e2) -> "(' " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Ident n -> n
    | BVar i -> "i" ^ string_of_int i
    | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Empty -> "^"
    | Shift n -> "^" ^ string_of_int n
    | Comma (e1, e2) -> "(, " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Semicolon (e1, e2) -> "(; " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Hole (Some s) -> "?" ^ s
    | Hole None -> "?"
    | Ctx -> "ctx"

  let rec print_pat (p : pat) : string = match p with
    | PIdent n -> n
    | Inacc e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ String.concat " " f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PClos (n, e) -> "([] " ^ n ^ " " ^ print_exp e ^ ")"
    | PBox (p1, p2) -> "(:> " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PEmpty -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PDot (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PComma (p1, None, p2) -> "(, " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PComma (p1, Some x, p2) -> "(, " ^ print_pat p1 ^ " " ^ x ^ " : " ^ print_pat p2 ^ ")"
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

module Apx = struct
  open Syntax.Apx
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
    | Lam (fs, e) -> "(\\ " ^ String.concat " " fs ^ " " ^ print_exp e ^ ")"
    | App (e, es) -> "(" ^ print_exp e ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    | AppL (e1, es) -> "(" ^ print_exp e1 ^ " ' " ^ String.concat " ' " (List.map print_exp es) ^ ")"
    | Const n -> n
    | Dest n -> n
    | Var n -> Name.print_name n
    | BVar i -> "i" ^ string_of_int i
    | Clos (e1, e2) -> "(" ^ print_exp e1 ^ " [" ^ print_exp e2 ^ "])"
    | Empty -> "^"
    | Shift n -> "^" ^ string_of_int n
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

  let rec print_pat (p : pat) : string = match p with
    | PVar n -> print_name n
    | PPar n -> "(<: " ^ print_name n ^ ")"
    | PBVar n -> "i" ^ string_of_int n
    | Inacc e -> "." ^ print_exp e
    | PLam (fs, p) -> "(\ " ^ String.concat " " fs ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PClos (n, s) -> print_name n ^ "[" ^ print_pat_subst s ^ "]"
    | SInacc (e, s) -> "." ^ print_exp e ^ "[" ^ print_pat_subst s ^ "]"
    | PEmpty -> "^"
    | PShift i -> "^ " ^ string_of_int i
    | PDot (p1, p2) -> "(" ^ print_pat p1 ^ " ; " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PSnoc (p1, x, p2) -> "(" ^ print_pat p1 ^ " , " ^ x ^ ":" ^ print_pat p2 ^ ")"
    | PUnder -> "_"
    | PWildcard -> "._"

  let print_tel (tel : tel) : string =
    String.concat ", " (List.map (fun (_, x, e) -> "(" ^ print_name x
                                                   ^ ", " ^ print_exp e ^ ")") tel)

  (* TODO use this in print_spi *)
  let print_stel (tel : stel) : string =
    String.concat ", " (List.map (fun (_, x, e) -> "(" ^ x ^ ", " ^ print_exp e ^ ")") tel)


  let print_dsig ((d, es) : dsig) = "(" ^ d ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"

  let print_decls (decls : decls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig) -> "(" ^ n ^ " " ^ print_tel tel
                                                   ^ " " ^ print_dsig dsig ^ ")") decls)

  let print_sdecls (decls : sdecls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig) -> "(" ^ n ^ " " ^ print_stel tel
                                                   ^ " " ^ print_dsig dsig ^ ")") decls)

  let print_codecls (decls : codecls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig, e) -> "(" ^ n ^ " " ^ print_tel tel
                    ^ " " ^ print_dsig dsig ^ " " ^ print_exp e ^ ")") decls)

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

  let print_program = function
    | Data (n, ps, is, u, decls) ->
      "(data " ^ n ^ " (" ^ print_params ps ^ ") (" ^ print_params is ^ ") " ^ print_universe u  ^ "\n" ^ print_decls decls ^ ")"
    | Codata (n, ps, is, u, decls) ->
       "(data " ^ n ^ " (" ^ print_params ps ^ ") (" ^ print_params is ^ ") " ^ print_universe u  ^ "\n" ^ print_codecls decls ^ ")"

    | Syn (n, tel, decls) -> "(syn " ^ n ^ " " ^ print_stel tel ^ "\n" ^ print_sdecls decls ^ ")"
    | DefPM (n, tel, e, decls) -> "(def " ^ n ^ " (" ^ print_tel tel ^ ") " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  end

module Int = struct
  open Syntax.Int
  open Name

  (* Pretty printer -- could be prettier *)
  let print_universe = string_of_int

  let rec print_exp = function
    | Set n -> print_universe n

    | Ctx -> "ctx"
    | Pi (tel, t) -> print_pi tel t

    | Box (ctx, e) -> "(" ^ print_bctx ctx ^ " |- " ^ print_syn_exp e ^ ")"
    | TermBox (ctx, se) -> "(" ^ print_bctx ctx ^ " :> " ^ print_syn_exp se ^ ")"
    | Fn (fs, e) -> "(fn " ^ (String.concat " " (List.map print_name fs)) ^ " " ^ print_exp e ^ ")"
    | App (e, es) -> "(" ^ print_exp e ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    | Const n -> n
    | Dest n -> n
    | Var n -> Name.print_name n
    | BCtx cP -> print_bctx cP
    | Annot (e1, e2) -> "(" ^ print_exp e1 ^ " : " ^ print_exp e2 ^ ")"
    | Hole s -> "?" ^ print_name s

  and print_syn_exp = function
    | Star -> "*"
    | SPi (tel, t) -> print_spi tel t
    | Lam (fs, e) ->
       "(\\ " ^ String.concat " " (List.map (fun (x, t) -> "("^ x ^ " : " ^ print_syn_exp t ^ ")") fs) ^ " " ^ print_syn_exp e ^ ")"
    | AppL (e1, es) -> "(" ^ print_syn_exp e1 ^ " ' " ^ String.concat " ' " (List.map print_syn_exp es) ^ ")"
    | BVar i -> "i" ^ string_of_int i
    | SConst n -> n ^ "%"
    | Empty -> "^"
    | Shift n -> "^" ^ string_of_int n
    | ShiftS (n, s) -> "(^^" ^ string_of_int n ^ " " ^ print_syn_exp s ^ ")"
    | Comp (e1, cP, e2) -> "(" ^ print_syn_exp e1 ^ " o" ^ print_bctx cP ^ " " ^ print_syn_exp e2 ^ ")"
    | Dot (s, e) -> "(" ^ print_syn_exp s ^ " ; " ^ print_syn_exp e ^ ")"
    | Clos (e, s, cP) -> "(" ^ print_syn_exp e ^ " [" ^ print_syn_exp s ^ " : " ^ print_bctx cP ^ "])"
    | Unbox (e, se, cP) -> "(ub " ^ print_exp e ^ "[" ^ print_syn_exp se ^ " : " ^ print_bctx cP  ^ "])"
    | SCtx -> "ctx"
    | SBCtx cP -> print_bctx cP

  and print_bctx cP =
    let rec print = function
    | Snoc (cP, x, e2) -> "(" ^ print  cP ^ ", " ^ x ^ " : " ^ print_syn_exp e2 ^ ")"
    | Nil -> "0"
    | CtxVar n -> print_name n
    in
    "{" ^ print cP ^ "}"

  and print_pi tel t = match tel with
    | [] -> print_exp t
    | (_, x, e) :: tel when is_name_floating x ->
       "(" ^ print_exp e ^ " -> " ^ print_pi tel t ^ ")"
    | (_, x, e) :: tel -> "(" ^ print_name x ^ " : " ^ print_exp e ^ ") -> " ^ print_pi tel t
  and print_spi tel t = match tel with
    | [] -> print_syn_exp t
    | (_, x, e) :: tel -> "(" ^ x ^ " : " ^ print_syn_exp e ^ ") ->> " ^ print_spi tel t

  let print_exps es = "(" ^ String.concat ", " (List.map print_exp es) ^ ")"
  let print_syn_exps es = "(" ^ String.concat ", " (List.map print_syn_exp es) ^ ")"

  let rec print_pat (p : pat) : string = match p with
    | PVar n -> print_name n
    | PPar n -> "(<: " ^ print_name n ^ ")"
    | Inacc e -> "." ^ print_exp e

    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PBCtx cP -> print_pat_bctx cP
    | PUnder -> "_"
    | PTBox (cP, p) -> "(" ^ print_bctx cP ^ " " ^ print_syn_pat p ^ ")"

  and print_syn_pat = function
    | PBVar i -> "i" ^ string_of_int i
    | PLam (fs, p) -> "(\ " ^ String.concat " " (List.map (fun (x, t) -> "("^ x ^ " : " ^ print_syn_exp t ^ ")") fs) ^ " " ^ print_syn_pat p ^ ")"
    | PSConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_syn_pat p ^ ")") ps)) ^ ")"
    | PUnbox (n, s, cP) -> "(u " ^ print_name n ^ "[" ^ print_pat_subst s ^ " : " ^ print_bctx cP ^ "])"
    | SInacc (e, s, cP) -> "(s. " ^ print_exp e ^ "[" ^ print_pat_subst s ^ " : " ^ print_bctx cP ^ "])"
    | PEmpty -> "^"
    | PShift i -> "^ " ^ string_of_int i
    | PDot (p1, p2) -> "(" ^ print_syn_pat p1 ^ " ; " ^ print_syn_pat p2 ^ ")"

  and print_pat_bctx = function
    | PNil -> "0"
    | PSnoc (cP, x, t) -> "(" ^ print_pat_bctx cP ^ " , " ^ x ^ print_syn_exp t ^ ")"
    | PCtxVar n -> print_name n

  let print_ctx = function
    | [] -> "[]"
    | [x, e] -> "[" ^ print_name x ^ " : " ^ print_exp e ^ "]"
    | c -> "[" ^ (String.concat ", " (List.map (fun (x, e) -> print_name x ^ ": " ^ print_exp e) c)) ^ "]"

  let print_tel (tel : tel) : string =
    String.concat ", " (List.map (fun (_, x, e) -> "(" ^ print_name x
                                                   ^ ", " ^ print_exp e ^ ")") tel)

  let print_stel (tel : stel) : string =
    String.concat ", " (List.map (fun (_, x, e) -> "(" ^ x ^ ", " ^ print_syn_exp e ^ ")") tel)


  let print_dsig ((d, es) : dsig) = "(" ^ d ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"

  let print_syn_dsig ((d, es) : syn_dsig) = "(" ^ d ^ " " ^ String.concat " " (List.map print_syn_exp es) ^ ")"

  let print_decls (decls : decls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig) -> "(" ^ n ^ " " ^ print_tel tel
                                                   ^ " " ^ print_dsig dsig ^ ")") decls)

  let print_sdecls (decls : sdecls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig) -> "(" ^ n ^ " " ^ print_stel tel
                                                   ^ " " ^ print_syn_dsig dsig ^ ")") decls)

  let print_codecls (decls : codecls) : string =
    String.concat "\n"
                  (List.map (fun (n, tel, dsig, e) -> "(" ^ n ^ " " ^ print_tel tel
                    ^ " " ^ print_dsig dsig ^ " " ^ print_exp e ^ ")") decls)

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

  let print_subst c = "[" ^ (String.concat ",\n" (List.map (fun (x, e) -> print_name x ^ " := " ^ print_exp e) c)) ^ "]"
  let print_psubst c = "[" ^ (String.concat ",\n" (List.map (fun (x, e) -> print_name x ^ " := " ^ print_pat e) c)) ^ "]"

  let print_program = function
    | Data (n, ps, is, u, decls) ->
      "(data " ^ n ^ " (" ^ print_params ps ^ ") (" ^ print_params is ^ ") " ^ print_universe u  ^ "\n" ^ print_decls decls ^ ")"
    | Codata (n, ps, is, u, decls) ->
       "(data " ^ n ^ " (" ^ print_params ps ^ ") (" ^ print_params is ^ ") " ^ print_universe u  ^ "\n" ^ print_codecls decls ^ ")"

    | Syn (n, tel, decls) -> "(syn " ^ n ^ " " ^ print_stel tel ^ "\n" ^ print_sdecls decls ^ ")"
    | DefPM (n, tel, e, decls) -> "(def " ^ n ^ " (" ^ print_tel tel ^ ") " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
end

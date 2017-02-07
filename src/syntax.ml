type icit = Explicit | Implicit

module Ext = struct

  type name = string

  type pats = name list

  type exp =
    | Star
    | Set of int
    | Arr of exp * exp
    | SArr of exp * exp
    | Box of exp * exp
    | TBox of exp * exp (* term box, only in external syntax *)
    | Fn of name * exp
    | Lam of name * exp
    | App of exp * exp
    | AppL of exp * exp
    | Ident of name
    | Clos of exp * exp
    | EmptyS
    | Shift of int
    | Comma of exp * exp
    | Semicolon of exp * exp
    | Nil
    | Annot of exp * exp

  type decls = (name * exp) list
  type def_decls = (pats * exp) list
  type param = icit * name * exp
  type params = param list

  type program =
    | Data of name * params * exp * decls
    | Syn of name * params * exp * decls
    | DefPM of name * exp * def_decls
    | Def of name * exp * exp

  let rec print_exp = function
    | Star -> "*"
    | Set n -> "set" ^ string_of_int n
    | Arr (t, e) -> "(-> " ^ print_exp t ^ " " ^ print_exp e ^ ")"
    | SArr (t, e) -> "(->> " ^ print_exp t ^ " " ^ print_exp e ^ ")"
    | Box (ctx, e) -> "(|- " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | TBox (ctx, e) -> "(:> " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | Fn (f, e) -> "(fn " ^ f ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\ " ^ f ^ " " ^ print_exp e ^ ")"
    | App (e1, e2) -> "(app " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | AppL (e1, e2) -> "(' " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Ident n -> n
    | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | EmptyS -> "^"
    | Shift n -> "^" ^ string_of_int n
    | Comma (e1, e2) -> "(, " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Semicolon (e1, e2) -> "(; " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

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

end

module Int = struct

  type name = string * int
  type index = int
  type def_name = string

  let gen_sym =
    let state = ref 0 in
    fun () -> state := !state + 1 ; !state - 1

  let gen_name s = (s, gen_sym ())

  let refresh_name (s, _) = (s, gen_sym())

  type pats = name list

  type exp =
    | Star
    | Set of int
    | Pi of name option * exp * exp (* A pi type *)
    | Arr of exp * exp       (* A syntactic type *)
    | Box of exp * exp
    | Fn of name * exp
    | Lam of string * exp
    | App of exp * exp
    | AppL of exp * exp
    | Const of def_name (* The name of a constant *)
    | Var of name
    | BVar of index
    | Clos of exp * exp
    | EmptyS
    | Shift of int
    | Comma of exp * exp
    | Subst of exp * exp
    | Nil
    | Annot of exp * exp

  type decls = (def_name * exp) list
  type pat_decls = (pats * exp) list

  type param = icit * name * exp
  type params = param list

  type program =
    | Data of def_name * params * exp * decls
    | Syn of def_name * params * exp * decls
    | DefPM of def_name * exp * pat_decls
    | Def of def_name * exp * exp

  (* Generate fresh names for all the variables, to keep names unique *)

  let refresh (e : exp) : exp =
    let rec refresh (rep : (name * name) list) : exp -> exp =
      let f x = refresh rep x in
      function
      | Star -> Star
      | Set n ->  Set n
      | Pi (Some n, s, t) ->
         let n' = refresh_name n in
         Pi (Some n', s, refresh ((n, n')::rep) t)
      | Pi (None, s, t) -> Pi (None, f s, f t)
      | Arr (t, e) -> Arr(f t, f e)
      | Box (ctx, e) -> Box(f ctx, f e)
      | Fn (x, e) ->
         let x' = refresh_name x in
         Fn (x', refresh ((x, x')::rep) e)
      | Lam (x, e) ->
         Lam(x, f e)
      | App (e1, e2) -> Arr(f e1, f e1)
      | AppL (e1, e2) -> Arr(f e1, f e1)
      | Const n -> Const n
      | Var n ->
         (try
           Var (List.assoc n rep)
         with
           Not_found -> Var n)
      | BVar i -> BVar i
      | Clos (e1, e2) -> Clos(f e1, f e1)
      | EmptyS -> EmptyS
      | Shift n -> Shift n
      | Comma (e1, e2) -> Comma(f e1, f e1)
      | Subst (e1, e2) -> Subst(f e1, f e1)
      | Nil -> Nil
      | Annot (e1, e2) -> Annot(f e1, f e1)
    in
    refresh [] e

  (* Substitution of regular variables *)

  let rec subst ((x, es) : name * exp) : exp ->  exp =
    let f e = subst (x, refresh es) e in
    function
    | Star -> Star
    | Set n ->  Set n
    | Pi (Some n, s, t) -> assert false
    | Pi (None, s, t) -> Pi (None, f s, f t)
    | Arr (t, e) -> Arr(f t, f e)
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (f, e) -> assert false
    | Lam (x, e) -> Lam(x, f e)
    | App (e1, e2) -> Arr(f e1, f e1)
    | AppL (e1, e2) -> Arr(f e1, f e1)
    | Const n -> Const n
    | Var n  when x = n -> refresh es
    | Var n -> Var n
    | BVar i -> BVar i
    | Clos (e1, e2) -> Clos(f e1, f e1)
    | EmptyS -> EmptyS
    | Shift n -> Shift n
    | Comma (e1, e2) -> Comma(f e1, f e1)
    | Subst (e1, e2) -> Subst(f e1, f e1)
    | Nil -> Nil
    | Annot (e1, e2) -> Annot(f e1, f e1)

  (* Pretty printer -- could be prettier *)

  let print_name (n, i) = n ^ "_" ^ string_of_int i

  let rec print_exp = function
    | Star -> "*"
    | Set n -> "set" ^ string_of_int n
    | Pi (Some n, s, t) -> "(pi " ^ print_name n ^ " " ^ print_exp s ^ print_exp s ^ ")"
    | Pi (None, s, t) -> "(-> " ^ print_exp s ^ " " ^ print_exp s ^ ")"
    | Arr (t, e) -> "(->> " ^ print_exp t ^ " " ^ print_exp e ^ ")"
    | Box (ctx, e) -> "(|- " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | Fn (f, e) -> "(fn " ^ print_name f ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\ " ^ f ^ " " ^ print_exp e ^ ")"
    | App (e1, e2) -> "(app " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | AppL (e1, e2) -> "(' " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Const n -> n
    | Var n -> print_name n
    | BVar i -> "(i " ^ string_of_int i ^ ")"
    | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | EmptyS -> "^"
    | Shift n -> "^" ^ string_of_int n
    | Comma (e1, e2) -> "(, " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Subst (e1, e2) -> "(; " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

  let print_decls decls = String.concat "\n" (List.map (fun (n, e) -> "(" ^ n ^ " " ^ print_exp e ^ ")") decls )
  let print_pats pats = String.concat " " (List.map print_name pats)
  let print_def_decls decls = String.concat "\n" (List.map (fun (pats, e) -> "(" ^ print_pats pats ^ " " ^ print_exp e ^ ")") decls)

  let print_param = function
    | Implicit, n, e -> "(:i " ^ print_name n ^ " " ^ print_exp e ^ ")"
    | Explicit, n, e -> "(:e " ^ print_name n ^ " " ^ print_exp e ^ ")"

  let print_params ps = String.concat " " (List.map print_param ps)

  let print_program = function
    | Data (n, ps, e, decls) -> "(data " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | Syn (n, ps, e, decls) -> "(syn " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | DefPM (n, e, decls) -> "(def " ^ n ^ " " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"


end

type icit = Explicit | Implicit

module Ext = struct

  type name = string

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
    | Under

  type pat =
    | PIdent of name
    | Innac of exp
    | PLam of name * pat
    | PConst of name * pat list
    | PAnnot of pat * exp
    | PClos of name * pat
    | PEmptyS
    | PShift of int
    | PSubst of pat * pat
    | PNil
    | PComma of pat * pat
    | PBox of pat * pat
    | PUnder

  type pats = pat list

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
    | Under -> "_"

  let rec print_pat (p : pat) : string = match p with
    | PIdent n -> n
    | Innac e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(Const " ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PAnnot (p, e) -> "(: " ^ print_pat p ^ " " ^ print_exp e ^ ")"
    | PClos (n, p) -> "([] " ^ n ^ " " ^ print_pat p ^ ")"
    | PBox (p1, p2) -> "(:> " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PEmptyS -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PSubst (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PComma (p1, p2) -> "(, " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PUnder -> "_"


  let print_decls decls = String.concat "\n" (List.map (fun (n, e) -> "(" ^ n ^ " " ^ print_exp e ^ ")") decls)
  let print_pats pats = String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") (List.rev pats))
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
    | Under

  type pat =
    | PVar of name
    | PBVar of index
    | Innac of exp
    | PLam of string * pat
    | PConst of def_name * pat list
    | PAnnot of pat * exp
    | PClos of name * pat
    | PEmptyS
    | PShift of int
    | PSubst of pat * pat
    | PNil
    | PComma of pat * pat
    | PUnder

  type pats = pat list

  type decls = (def_name * exp) list
  type pat_decls = (pats * exp) list

  type param = icit * name * exp
  type params = param list

  type program =
    | Data of def_name * params * exp * decls
    | Syn of def_name * params * exp * decls
    | DefPM of def_name * exp * pat_decls
    | Def of def_name * exp * exp

  let rec fv =
    let (--) l n = List.filter ((!=) n) l in
    function
    | Star -> []
    | Set n ->  []
    | Pi (Some n, s, t) -> fv s @ (fv t -- n)
    | Pi (None, s, t) -> fv s @ fv t
    | Arr (t, e) -> fv t @ fv e
    | Box (ctx, e) -> fv ctx @ fv e
    | Fn (x, e) -> (fv e -- x)
    | Lam (x, e) -> fv e
    | App (e1, e2) -> fv e1 @ fv e2
    | AppL (e1, e2) -> fv e1 @ fv e2
    | Const n -> []
    | Var n -> [n]
    | BVar i -> []
    | Clos (e1, e2) -> fv e1 @ fv e2
    | EmptyS -> []
    | Shift n -> []
    | Comma (e1, e2) -> fv e1 @ fv e2
    | Subst (e1, e2) -> fv e1 @ fv e2
    | Nil -> []
    | Annot (e1, e2) -> fv e1 @ fv e2
    | Under -> []

  (* Generate fresh names for all the bound variables,
     to keep names unique *)

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
      | Under -> Under
    in
    refresh [] e

  (* refresh one free variable *)
  let rec refresh_free_var (x , y : name * name) (e : exp) : exp =
    let f e = refresh_free_var (x, y) e in
    match e with
    | Star -> Star
    | Set n ->  Set n
    | Pi (Some n, _, _) when n = x -> raise (Error.Violation "Duplicate variable name")
    | Pi (n, s, t) -> Pi (n, f s, f t)
    | Arr (t, e) -> Arr(f t, f e)
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (n, _) when n = x -> raise (Error.Violation "Duplicate variable name")
    | Fn (x, e) -> Fn (x, f e)
    | Lam (x, e) -> Lam(x, f e)
    | App (e1, e2) -> Arr(f e1, f e1)
    | AppL (e1, e2) -> Arr(f e1, f e1)
    | Const n -> Const n
    | Var n when n = x -> Var y
    | Var n -> Var n
    | BVar i -> BVar i
    | Clos (e1, e2) -> Clos(f e1, f e1)
    | EmptyS -> EmptyS
    | Shift n -> Shift n
    | Comma (e1, e2) -> Comma(f e1, f e1)
    | Subst (e1, e2) -> Subst(f e1, f e1)
    | Nil -> Nil
    | Annot (e1, e2) -> Annot(f e1, f e1)
    | Under -> Under

  (* Substitution of regular variables *)

  (* TODO: do the refreshing while substituting, otherwise it
     might be really slow. *)

  let rec subst ((x, es) : name * exp) (e : exp) :  exp =
    let f e = subst (x, es) e in
    if List.mem x (fv es) then raise (Error.Violation "Duplicate variable name in substitution.") ;
    match e with
    | Star -> Star
    | Set n ->  Set n
    | Pi (Some n, s, t) ->
       let n' = refresh_name n in
       (* the following cannot happen because n' is just fresh *)
       (* if List.mem n' (fv es) then raise (Error.Violation "Duplicate variable name would be captured.") ; *)
       Pi (Some n', s, subst (x, es) (refresh_free_var (n, n') t))
    | Pi (None, s, t) -> Pi (None, f s, f t)
    | Arr (t, e) -> Arr(f t, f e)
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (y, e) ->
       let y' = refresh_name y in
       (* the following cannot happen because y' is just fresh *)
       (* if List.mem y' (fv es) then raise (Error.Violation "Duplicate variable name would be captured.") ; *)
       Fn(y', subst (x, es) (refresh_free_var (y, y') e))
    | Lam (x, e) -> Lam(x, f e)
    | App (e1, e2) -> App(f e1, f e2)
    | AppL (e1, e2) -> AppL(f e1, f e2)
    | Const n -> Const n
    | Var n  when x = n -> refresh es
    | Var n -> Var n
    | BVar i -> BVar i
    | Clos (e1, e2) -> Clos(f e1, f e2)
    | EmptyS -> EmptyS
    | Shift n -> Shift n
    | Comma (e1, e2) -> Comma(f e1, f e2)
    | Subst (e1, e2) -> Subst(f e1, f e2)
    | Nil -> Nil
    | Annot (e1, e2) -> Annot(f e1, f e2)
    | Under -> Under

  (* Pretty printer -- could be prettier *)

  let print_name (n, i) = n ^ "_" ^ string_of_int i

  let rec print_exp = function
    | Star -> "*"
    | Set n -> "set" ^ string_of_int n
    | Pi (Some n, s, t) -> "(pi " ^ print_name n ^ " " ^ print_exp s ^ " " ^ print_exp t ^ ")"
    | Pi (None, s, t) -> "(-> " ^ print_exp s ^ " " ^ print_exp t ^ ")"
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
    | Under -> "_"

  let rec print_pat (p : pat) : string = match p with
    | PVar n -> print_name n
    | PBVar i -> "(i " ^ string_of_int i ^ ")"
    | Innac e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(Const " ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PAnnot (p, e) -> "(: " ^ print_pat p ^ " " ^ print_exp e ^ ")"
    | PClos (n, p) -> "([] " ^ print_name n ^ " " ^ print_pat p ^ ")"
    | PEmptyS -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PSubst (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PComma (p1, p2) -> "(, " ^ print_pat p1 ^ " " ^ print_pat p1 ^ ")"
    | PUnder -> "_"

  let print_decls decls = String.concat "\n" (List.map (fun (n, e) -> "(" ^ n ^ " " ^ print_exp e ^ ")") decls )
  let print_pats pats = String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") (List.rev pats))
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

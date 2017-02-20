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
    | Fn of name list * exp
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
    | PWildcard                 (* Inaccessible pattern wildcard *)

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
    | Fn (fs, e) ->
       "(fn " ^ (String.concat " " fs) ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\ " ^ f ^ " " ^ print_exp e ^ ")"
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
    | Under -> "_"

  let rec print_pat (p : pat) : string = match p with
    | PIdent n -> n
    | Innac e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PAnnot (p, e) -> "(: " ^ print_pat p ^ " " ^ print_exp e ^ ")"
    | PClos (n, p) -> "([] " ^ n ^ " " ^ print_pat p ^ ")"
    | PBox (p1, p2) -> "(:> " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PEmptyS -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PSubst (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PComma (p1, p2) -> "(, " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PUnder -> "_"
    | PWildcard -> "._"


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
  open Name

  type index = int
  type def_name = string

  let (--) l n = List.filter ((!=) n) l

  type universe
    = Star
    | Set of int

  type exp
    = Univ of universe
    | Pi of tel * exp  (* A pi type *)
    | Arr of exp * exp (* A syntactic type *)
    | Box of exp * exp
    | Fn of name list * exp
    | Lam of string * exp
    | App of exp * exp list
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

   and tel_entry = icit * name * exp
   and tel = tel_entry list

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
    | PWildcard

  type pats = pat list

  type decls = (def_name * exp) list
  type pat_decls = (pats * exp) list

  type program =
    | Data of def_name * tel * exp * decls
    | Syn of def_name * tel * exp * decls
    | DefPM of def_name * exp * pat_decls
    | Def of def_name * exp * exp

  let rec fv =
    function
    | Univ _ -> []
    | Pi (tel, t) ->fv_tel tel t
    | Arr (t, e) -> fv t @ fv e
    | Box (ctx, e) -> fv ctx @ fv e
    | Fn (xs, e) ->
       List.fold_left (fun vars x -> vars -- x) (fv e) xs
    | Lam (x, e) -> fv e
    | App (e1, es) -> fv e1 @ List.concat (List.map fv es)
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

  and fv_tel (tel : tel) (t : exp) = match tel with
    | [] -> fv t
    | (_, n, e)::tel -> fv e @ (fv_tel tel t -- n)

  (* Generate fresh names for all the bound variables,
     to keep names unique *)

  let refresh (e : exp) : exp =
    let rec refresh (rep : (name * name) list) : exp -> exp =
      let f x = refresh rep x in
      function
      | Univ u -> Univ u
      | Pi (tel, t) -> let tel', t' = refresh_tel rep tel t in Pi(tel', t')
      | Arr (t, e) -> Arr(f t, f e)
      | Box (ctx, e) -> Box(f ctx, f e)
      | Fn (xs, e) ->
         let xs' = List.map refresh_name xs in
         let extra = List.map2 (fun x y -> x, y) xs xs in
         Fn (xs', refresh (extra @ rep) e)
      | Lam (x, e) ->
         Lam(x, f e)
      | App (e1, es) -> App(f e1, List.map f es)
      | AppL (e1, e2) -> AppL(f e1, f e2)
      | Const n -> Const n
      | Var n ->
         (try
           Var (List.assoc n rep)
         with
           Not_found -> Var n)
      | BVar i -> BVar i
      | Clos (e1, e2) -> Clos(f e1, f e2)
      | EmptyS -> EmptyS
      | Shift n -> Shift n
      | Comma (e1, e2) -> Comma(f e1, f e2)
      | Subst (e1, e2) -> Subst(f e1, f e2)
      | Nil -> Nil
      | Annot (e1, e2) -> Annot(f e1, f e2)
      | Under -> Under

    and refresh_tel (rep : (name * name) list) (tel : tel) (t : exp) : tel * exp =
      match tel with
      | [] -> [], refresh rep t
      | (i, n, e) :: tel ->
         let n' = refresh_name n in
         let tel', t' = refresh_tel ((n, n')::rep) tel t in
         ((i, n', refresh rep e)::tel'), t'
    in
    refresh [] e

  (* refresh one free variable *)
  let rec refresh_free_var (x , y : name * name) (e : exp) : exp =
    let f e = refresh_free_var (x, y) e in
    match e with
    | Univ u -> Univ u
    | Pi (tel, t) ->
       let tel', t' = refresh_free_var_tel (x, y) tel t in
       Pi (tel', t')
    | Arr (t, e) -> Arr(f t, f e)
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (xs, _) when List.mem x xs -> raise (Error.Violation "Duplicate variable name")
    | Fn (xs, e) -> Fn (xs, f e)
    | Lam (x, e) -> Lam(x, f e)
    | App (e1, es) -> App(f e1, List.map f es)
    | AppL (e1, e2) -> AppL(f e1, f e2)
    | Const n -> Const n
    | Var n when n = x -> Var y
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
  and refresh_free_var_tel (x, y) tel t =
    match tel with
    | [] -> [], refresh_free_var (x, y) t
    | (i, n, e) :: tel when n = x ->  raise (Error.Violation "Duplicate variable name")
    | (i, n, e) :: tel ->
       let tel', t' = refresh_free_var_tel (x, y) tel t in
       (i, n, refresh_free_var (x, y) e) :: tel', t'

  let refresh_free_vars (rep : (name * name) list) e =
    List.fold_left (fun e (y, y') -> refresh_free_var (y, y') e) e rep

  (* Substitution of regular variables *)

  let rec subst (x, es : name * exp) (e : exp) :  exp =
    let f e = subst (x, es) e in
    match e with
    | Univ u -> Univ u
    | Pi (tel, t) ->
       let tel', t' = subst_tel (x, es) tel t in
       Pi(tel', t')
    | Arr (t, e) -> Arr(f t, f e)
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (ys, e) ->
       let ys' = List.map refresh_name ys in
       (* the following cannot happen because y' is just fresh *)
       (* if List.mem y' (fv es) then raise (Error.Violation
       "Duplicate variable name would be captured.") ; *)
       let extra = List.map2 (fun x y -> x, y) ys ys' in
       Fn(ys', subst (x, es) (refresh_free_vars extra e))
    | Lam (x, e) -> Lam(x, f e)
    | App (e1, es) -> App(f e1, List.map f es)
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
  and subst_tel (x, es) tel t =
    match tel with
    | [] -> [], subst (x, es) t
    | (i, n, e) :: tel ->
       let n' = refresh_name n in
       (* the following cannot happen because n' is just fresh *)
       (* if List.mem n' (fv es) then raise (Error.Violation "Duplicate variable name would be captured.") ; *)
       let tel', t' = refresh_free_var_tel (n, n') tel t in
       let tel'', t'' = subst_tel (x, es) tel' t' in
       (i, n', subst (x, es) e) :: tel'', t''

  let subst_list sigma e =
    List.fold_left (fun e s -> subst s e) e sigma

  (* Pretty printer -- could be prettier *)
  let print_universe = function
    | Star -> "*"
    | Set n -> "set_" ^ string_of_int n

  let rec print_exp = function
    | Univ u -> print_universe u
    | Pi (tel, t) -> print_tel tel t
    | Arr (t, e) -> "(->> " ^ print_exp t ^ " " ^ print_exp e ^ ")"
    | Box (ctx, e) -> "(|- " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | Fn (fs, e) -> "(fn " ^ (String.concat " " (List.map print_name fs)) ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\ " ^ f ^ " " ^ print_exp e ^ ")"
    | App (e, es) -> "(" ^ print_exp e ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    | AppL (e1, e2) -> "(' " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Const n -> n
    | Var n -> Name.print_name n
    | BVar i -> "(i " ^ string_of_int i ^ ")"
    | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | EmptyS -> "^"
    | Shift n -> "^" ^ string_of_int n
    | Comma (e1, e2) -> "(, " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Subst (e1, e2) -> "(; " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Under -> "_"
  and print_tel tel t = match tel with
    | [] -> print_exp t
    | (_, x, e) :: tel when is_name_floating x ->
       "(-> " ^ print_exp e ^ " " ^ print_tel tel t ^ ")"
    | (_, x, e) :: tel -> "(pi " ^ print_name x ^ " " ^ print_exp e ^ " " ^ print_tel tel t ^ ")"

  let rec print_pat (p : pat) : string = match p with
    | PVar n -> print_name n
    | PBVar i -> "(i " ^ string_of_int i ^ ")"
    | Innac e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PAnnot (p, e) -> "(: " ^ print_pat p ^ " " ^ print_exp e ^ ")"
    | PClos (n, p) -> "([] " ^ print_name n ^ " " ^ print_pat p ^ ")"
    | PEmptyS -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PSubst (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PComma (p1, p2) -> "(, " ^ print_pat p1 ^ " " ^ print_pat p1 ^ ")"
    | PUnder -> "_"
    | PWildcard -> "._"

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

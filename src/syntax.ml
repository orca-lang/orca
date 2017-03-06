type icit = Explicit | Implicit

module Ext = struct

  type name = string

  type exp = raw_exp Location.t
   and raw_exp
     = Star
     | Set of int
     | Arr of exp * exp
     | SArr of exp * exp
     | Box of exp * exp
     | TBox of exp * exp (* term box, only in external syntax *)
     | Fn of name list * exp
     | Lam of name list * exp
     | App of exp * exp
     | AppL of exp * exp
     | Hole of name option
     | Ident of name
     | Clos of exp * exp
     | EmptyS
     | Shift of int
     | Comma of exp * exp
     | Semicolon of exp * exp
     | Nil
     | Annot of exp * exp
     | Under
     | Ctx

  type pat =
    | PIdent of name
    | Innac of exp
    | PLam of name list * pat
    | PConst of name * pat list
    | PAnnot of pat * exp
    | PClos of name * pat
    | PEmptyS
    | PShift of int
    | PSubst of pat * pat
    | PNil
    | PComma of pat *  pat
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
    | Syn of name * exp * decls
    | DefPM of name * exp * def_decls
    | Def of name * exp * exp

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
    | Under -> "_"
    | Hole (Some s) -> "?" ^ s
    | Hole None -> "?"
    | Ctx -> "ctx"

  let rec print_pat (p : pat) : string = match p with
    | PIdent n -> n
    | Innac e -> "(. " ^ print_exp e ^ ")"
    | PLam (f, p) -> "(\ " ^ String.concat " " f ^ " " ^ print_pat p ^ ")"
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
  let print_pats pats = String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") pats)
  let print_def_decls decls = String.concat "\n" (List.map (fun (pats, e) -> "(" ^ print_pats pats ^ " " ^ print_exp e ^ ")") decls)

  let print_param = function
    | Implicit, n, e -> "(:i " ^ n ^ " " ^ print_exp e ^ ")"
    | Explicit, n, e -> "(:e " ^ n ^ " " ^ print_exp e ^ ")"

  let print_params ps = String.concat " " (List.map print_param ps)

  let print_program = function
    | Data (n, ps, e, decls) -> "(data " ^ n ^ " " ^ print_params ps ^ "  " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | Syn (n, e, decls) -> "(syn " ^ n ^ " " ^ print_exp e ^ "\n" ^ print_decls decls ^ ")"
    | DefPM (n, e, decls) -> "(def " ^ n ^ " " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

end

module Int = struct
  open Name

  type index = int
  type universe = int
  type def_name = string

  let (--) l n = List.filter ((<>) n) l

  type exp
    = Set of universe
    | Star (* Universe of syntax *)
    | Pi of tel * exp  (* A pi type *)
    | SPi of stel * exp (* A syntactic type *)
    | Box of exp * exp
    | Ctx (* of exp *) (* Let's think about it *)
    | Const of def_name (* The name of a constant *)
    | Var of name
    | Fn of name list * exp
    | App of exp * exp list
    | Lam of string list * exp
    | AppL of exp * exp list
    | BVar of index
    | Clos of exp * exp
    | EmptyS
    | Shift of int
    | Dot of exp * exp
    | Comp of exp * exp
    | ShiftS of exp (* consider shifting by more than one, to improve efficiency *)
    | Snoc of exp * string * exp
    | Nil
    | Annot of exp * exp
    | Under
    | Hole of name

   and tel_entry = icit * name * exp
   and tel = tel_entry list

   and stel_entry = icit * string * exp
   and stel = stel_entry list

  type pat =
    | PVar of name
    | PBVar of index
    | Innac of exp
    | PLam of string list * pat
    | PConst of def_name * pat list
    | PAnnot of pat * exp
    | PClos of name * pat
    | PEmptyS
    | PShift of int
    | PDot of pat * pat
    | PNil
    | PSnoc of pat * string * pat
    | PUnder
    | PWildcard

  type pats = pat list
  (* name of the constructed type, the type parameters, and the indices *)
  type dsig = def_name * exp list
  type decls = (def_name * tel * dsig) list
  type sdecls = (def_name * stel * dsig) list
  type rhs
    = Just of exp
    | Impossible of name
  type pat_decls = (pats * rhs) list

  type program =
    (* name, parameters, indices, universe *)
    | Data of def_name * tel * tel * universe * decls
    | Syn of def_name * tel * decls
    | DefPM of def_name * tel * exp * pat_decls
    | Def of def_name * exp * exp

  let rec fv cG =
    let fv e = fv cG e in
    let rec in_ctx n = function
      | (x, _) :: _ when x = n -> true
      | _ :: cG -> in_ctx n cG
      | [] -> false
    in
    function
    | Set _ -> []
    | Star -> []
    | Ctx -> []
    | Pi (tel, t) -> fv_pi cG tel t
    | SPi (tel, e) -> fv_spi cG tel e
    | Box (ctx, e) -> fv ctx @ fv e
    | Fn (xs, e) ->
       List.fold_left (fun vars x -> vars -- x) (fv e) xs
    | Lam (x, e) -> fv e
    | App (e1, es) -> fv e1 @ List.concat (List.map fv es)
    | AppL (e, es) -> fv e @ List.concat (List.map fv es)
    | Const n -> []
    | Var n when in_ctx n cG -> []
    | Var n -> [n]
    | BVar i -> []
    | Clos (e1, e2) -> fv e1 @ fv e2
    | EmptyS -> []
    | Shift n -> []
    | Comp (e1, e2)
    | Dot (e1, e2) -> fv e1 @ fv e2
    | ShiftS e -> fv e
    | Snoc (g, _, e) -> fv g @ fv e
    | Nil -> []
    | Annot (e1, e2) -> fv e1 @ fv e2
    | Under -> []
    | Hole _ -> []

  and fv_pi cG (tel : tel) (t : exp) = match tel with
    | [] -> fv cG t
    | (_, n, e)::tel -> fv cG e @ (fv_pi cG tel t -- n)

  and fv_spi cG (tel : stel) (t : exp) = match tel with
    | [] -> fv cG t
    | (_, n, e)::tel -> fv cG e @ (fv_spi cG tel t)


  let rec fv_pat =
    function
    | PVar n -> [n]
    | PBVar i -> []
    | Innac e -> []
    | PLam (f, p) -> fv_pat p
    | PConst (n, ps) -> fv_pats ps
    | PAnnot (p, e) -> fv_pat p
    | PClos (n, p) ->  fv_pat p
    | PEmptyS -> []
    | PShift i -> []
    | PDot (p1, p2) -> fv_pat p1 @ fv_pat p2
    | PNil -> []
    | PSnoc (p1, _, p2) -> fv_pat p1 @ fv_pat p2
    | PUnder -> []
    | PWildcard -> []

  and fv_pats ps = List.concat(List.map fv_pat ps)

  (* Generate fresh names for all the bound variables,
     to keep names unique *)

  let refresh (e : exp) : exp =
    let rec refresh (rep : (name * name) list) : exp -> exp =
      let f x = refresh rep x in
      function
      | Set n -> Set n
      | Star -> Star
      | Ctx -> Ctx
      | Pi (tel, t) -> let tel', t' = refresh_tel rep tel t in Pi(tel', t')
      | SPi (tel, t) -> let tel', t' = refresh_stel rep tel t in SPi(tel', t')
      | Box (ctx, e) -> Box(f ctx, f e)
      | Fn (xs, e) ->
         let xs' = List.map refresh_name xs in
         let extra = List.map2 (fun x y -> x, y) xs xs in
         Fn (xs', refresh (extra @ rep) e)
      | Lam (x, e) ->
         Lam(x, f e)
      | App (e1, es) -> App(f e1, List.map f es)
      | AppL (e1, es) -> AppL(f e1, List.map f es)
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
      | Comp (e1, e2) -> Comp (f e1, f e2)
      | ShiftS e -> ShiftS (f e)
      | Dot (e1, e2) -> Dot (f e1, f e2)
      | Snoc (e1, x, e2) -> Snoc (f e1, x, f e2)
      | Nil -> Nil
      | Annot (e1, e2) -> Annot(f e1, f e2)
      | Under -> Under
      | Hole s -> Hole s

    and refresh_tel (rep : (name * name) list) (tel : tel) (t : exp) : tel * exp =
      match tel with
      | [] -> [], refresh rep t
      | (i, n, e) :: tel ->
         let n' = refresh_name n in
         let tel', t' = refresh_tel ((n, n')::rep) tel t in
         ((i, n', refresh rep e)::tel'), t'

    and refresh_stel (rep : (name * name) list) (tel : stel) (t : exp) : stel * exp =
      match tel with
      | [] -> [], refresh rep t
      | (i, n, e) :: tel ->
         let tel', t' = refresh_stel rep tel t in
         ((i, n, refresh rep e)::tel'), t'
    in
    refresh [] e

  (* refresh one free variable *)
  let rec refresh_free_var (x , y : name * name) (e : exp) : exp =
    let f e = refresh_free_var (x, y) e in
    match e with
    | Set n -> Set n
    | Star -> Star
    | Ctx -> Ctx
    | Pi (tel, t) ->
       let tel', t' = refresh_free_var_tel (x, y) tel t in
       Pi (tel', t')
    | SPi (tel, t) ->
       let tel', t' = refresh_free_var_stel (x, y) tel t in
       SPi (tel', t')
    | Box (ctx, e) -> Box(f ctx, f e)
    | Fn (xs, _) when List.mem x xs -> raise (Error.Violation "Duplicate variable name")
    | Fn (xs, e) -> Fn (xs, f e)
    | Lam (x, e) -> Lam(x, f e)
    | App (e1, es) -> App(f e1, List.map f es)
    | AppL (e1, es) -> AppL(f e1, List.map f es)
    | Const n -> Const n
    | Var n when n = x -> Var y
    | Var n -> Var n
    | BVar i -> BVar i
    | Clos (e1, e2) -> Clos(f e1, f e2)
    | EmptyS -> EmptyS
    | Shift n -> Shift n
    | Comp (e1, e2) -> Comp (f e1, f e2)
    | ShiftS e -> ShiftS (f e)
    | Dot (e1, e2) -> Dot (f e1, f e2)
    | Snoc (g, x, e2) -> Snoc(f g, x, f e2)
    | Nil -> Nil
    | Annot (e1, e2) -> Annot(f e1, f e2)
    | Under -> Under
    | Hole s -> Hole s
  and refresh_free_var_tel (x, y) tel t =
    match tel with
    | [] -> [], refresh_free_var (x, y) t
    | (i, n, e) :: tel when n = x ->  raise (Error.Violation "Duplicate variable name")
    | (i, n, e) :: tel ->
       let tel', t' = refresh_free_var_tel (x, y) tel t in
       (i, n, refresh_free_var (x, y) e) :: tel', t'
  and refresh_free_var_stel (x, y) tel t =
    match tel with
    | [] -> [], refresh_free_var (x, y) t
    | (i, n, e) :: tel ->
       let tel', t' = refresh_free_var_stel (x, y) tel t in
       (i, n, refresh_free_var (x, y) e) :: tel', t'


  let refresh_free_vars (rep : (name * name) list) e =
    List.fold_left (fun e (y, y') -> refresh_free_var (y, y') e) e rep

  (* Substitution of regular variables *)

  type single_subst = name * exp
  type subst = single_subst list
  type single_psubst = name * pat
  type psubst = single_psubst list

  let fv_subst cG sigma = List.concat (List.map (fun (n, e) -> fv cG e -- n) sigma)

  let rec subst (x, es : single_subst) (e : exp) :  exp =
    let f e = subst (x, es) e in
    match e with
    | Set n -> Set n
    | Star -> Star
    | Ctx -> Ctx
    | Pi (tel, t) ->
       let tel', t' = subst_pi (x, es) tel t in
       Pi(tel', t')
    | SPi (tel, t) ->
      let tel', t' = subst_spi (x, es) tel t in
       SPi(tel', t')
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
    | AppL (e1, es) -> AppL(f e1, List.map f es)
    | Const n -> Const n
    | Var n  when x = n -> refresh es
    | Var n -> Var n
    | BVar i -> BVar i
    | Clos (e1, e2) -> Clos(f e1, f e2)
    | EmptyS -> EmptyS
    | Shift n -> Shift n
    | ShiftS e -> ShiftS (f e)
    | Comp (e1, e2) -> Comp (f e1, f e2)
    | Dot (e1, e2) -> Dot (f e1, f e2)
    | Snoc (e1, x, e2) -> Snoc (f e1, x, f e2)
    | Nil -> Nil
    | Annot (e1, e2) -> Annot(f e1, f e2)
    | Under -> Under
    | Hole s -> Hole s
  and subst_pi (x, es) tel t =
    match tel with
    | [] -> [], subst (x, es) t
    | (i, n, e) :: tel ->
       let n' = refresh_name n in
       (* the following cannot happen because n' is just fresh *)
       (* if List.mem n' (fv es) then raise (Error.Violation "Duplicate variable name would be captured.") ; *)
       let tel', t' = refresh_free_var_tel (n, n') tel t in
       let tel'', t'' = subst_pi (x, es) tel' t' in
       (i, n', subst (x, es) e) :: tel'', t''
  and subst_spi (x, es) tel t =
    match tel with
    | [] -> [], subst (x, es) t
    | (i, n, e) :: tel ->
       let tel', t' = subst_spi (x, es) tel t in
       (i, n, subst (x, es) e) :: tel', t'

  let simul_subst sigma e =
    List.fold_left (fun e s -> subst s e) e sigma

  let simul_subst_on_tel sigma tel =
    List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

  let simul_subst_on_stel sigma tel =
    List.map (fun (i, x, e) -> (i, x, simul_subst sigma e)) tel

  let rec compose_single_with_subst s = function
    | [] -> []
    | (y, t') :: sigma -> (y, subst s t') :: (compose_single_with_subst s sigma)

  let compose_subst sigma delta = List.map (fun (x, t) -> x, simul_subst sigma t) delta

  let rec psubst ((x, p') as s) (p : pat) :  pat =
    match p with
    | PVar n when n = x -> p'
    | PVar n -> PVar n
    | PBVar i -> PBVar i
    | Innac e -> Innac e        (* MMMMM *)
    | PLam (f, p) -> PLam(f, psubst s p)
    | PConst (n, ps) -> PConst(n, List.map (psubst s) ps)
    | PAnnot (p, e) -> PAnnot(psubst s p, e) (* MMMM should we remove PAnnot? Yaasss *)
    | PClos (n, p) when n = x -> assert false (* MMMMMMM *)
    | PClos (n, p) -> PClos (n, psubst s p)
    | PEmptyS -> PEmptyS
    | PShift i -> PShift i
    | PDot (p1, p2) -> PDot (psubst s p1, psubst s p2)
    | PNil -> PNil
    | PSnoc (p1, x, p2) -> PSnoc (psubst s p1, x, psubst s p2)
    | PUnder -> PUnder
    | PWildcard -> PWildcard

  let rec compose_single_with_psubst s = function
    | [] -> []
    | (y, t') :: sigma -> (y, psubst s t') :: (compose_single_with_psubst s sigma)

  let pats_of_psubst : psubst -> pats = List.map snd

  let simul_psubst sigma p =
    List.fold_left (fun p s -> psubst s p) p sigma

  let simul_psubst_on_list sigma ps =
    List.map (simul_psubst sigma) ps

  let compose_psubst sigma delta = List.map (fun (x, t) -> x, simul_psubst sigma t) delta

  let exp_list_of_tel tel = List.map (fun (_, _, s) -> s) tel

  (* Pretty printer -- could be prettier *)
  let print_universe = string_of_int

  let rec print_exp = function
    | Set n -> print_universe n
    | Star -> "*"
    | Ctx -> "ctx"
    | Pi (tel, t) -> print_pi tel t
    | SPi (tel, t) -> print_spi tel t
    | Box (ctx, e) -> "(|- " ^ print_exp ctx ^ " " ^ print_exp e ^ ")"
    | Fn (fs, e) -> "(fn " ^ (String.concat " " (List.map print_name fs)) ^ " " ^ print_exp e ^ ")"
    | Lam (f, e) -> "(\\ " ^ String.concat " " f ^ " " ^ print_exp e ^ ")"
    | App (e, es) -> "(" ^ print_exp e ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    | AppL (e1, es) -> "(' " ^ print_exp e1 ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    | Const n -> n
    | Var n -> Name.print_name n
    | BVar i -> "(i " ^ string_of_int i ^ ")"
    | Clos (e1, e2) -> "([] " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | EmptyS -> "^"
    | Shift n -> "^" ^ string_of_int n
    | ShiftS e -> "(^^ " ^ print_exp e ^ ")"
    | Comp (e1, e2) -> "(o " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Dot (e1, e2) -> "(; " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Snoc (e1, x, e2) -> "(, " ^ print_exp e1 ^ ", " ^ x ^ " : " ^ print_exp e2 ^ ")"
    | Nil -> "0"
    | Annot (e1, e2) -> "(: " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
    | Under -> "_"
    | Hole s -> "?" ^ print_name s
  and print_pi tel t = match tel with
    | [] -> print_exp t
    | (_, x, e) :: tel when is_name_floating x ->
       "(-> " ^ print_exp e ^ " " ^ print_pi tel t ^ ")"
    | (_, x, e) :: tel -> "(pi " ^ print_name x ^ " " ^ print_exp e ^ " " ^ print_pi tel t ^ ")"
  and print_spi tel t = match tel with
    | [] -> print_exp t
    | (_, x, e) :: tel -> "(spi " ^ x ^ " " ^ print_exp e ^ " " ^ print_spi tel t ^ ")"

  let print_exps es = "(" ^ String.concat ", " (List.map print_exp es) ^ ")"

  let rec print_pat (p : pat) : string = match p with
    | PVar n -> print_name n
    | PBVar i -> "(i " ^ string_of_int i ^ ")"
    | Innac e -> "." ^ print_exp e
    | PLam (f, p) -> "(\ " ^ String.concat " " f ^ " " ^ print_pat p ^ ")"
    | PConst (n, ps) -> "(" ^ n ^ " " ^ (String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)) ^ ")"
    | PAnnot (p, e) -> "(: " ^ print_pat p ^ " " ^ print_exp e ^ ")"
    | PClos (n, p) -> "([] " ^ print_name n ^ " " ^ print_pat p ^ ")"
    | PEmptyS -> "^"
    | PShift i -> "(^ " ^ string_of_int i ^ ")"
    | PDot (p1, p2) -> "(; " ^ print_pat p1 ^ " " ^ print_pat p2 ^ ")"
    | PNil -> "0"
    | PSnoc (p1, x, p2) -> "(, " ^ print_pat p1 ^ ", " ^ x ^ ":" ^ print_pat p1 ^ ")"
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
    | Syn (n, tel, decls) -> "(syn " ^ n ^ " " ^ print_tel tel ^ "\n" ^ print_decls decls ^ ")"
    | DefPM (n, tel, e, decls) -> "(def " ^ n ^ " (" ^ print_tel tel ^ ") " ^ print_exp e ^ "\n" ^ print_def_decls decls ^ ")"
    | Def (n, e1, e2) -> "(def " ^ n ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"

  let rec exp_of_pat : pat -> exp = function
    | PVar n -> Var n
    | PBVar i -> BVar i
    | Innac e -> e
    | PLam (f, p) -> Lam (f, exp_of_pat p)
    | PConst (n, ps) -> App (Const n, List.map exp_of_pat ps)
    | PAnnot (p, e) -> Annot (exp_of_pat p, e)
    | PClos (n, p) -> Clos (Var n, exp_of_pat p)
    | PEmptyS -> EmptyS
    | PShift i -> Shift i
    | PDot (p1, p2) -> Dot (exp_of_pat p1, exp_of_pat p2)
    | PNil -> Nil
    | PSnoc (p1, x, p2) -> Snoc (exp_of_pat p1, x, exp_of_pat p2)
    | PUnder -> Under
    | PWildcard -> raise (Error.Violation "We'd also be very surprised if this were to happen.")
end

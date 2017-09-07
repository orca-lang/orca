type icit = Explicit | Implicit
type def_name = string

type pat_subst
  = CShift of int
  | CEmpty
  | CDot of pat_subst * int

let pid_sub = CShift 0

module Ext = struct

  type name = string
  module N = Name

  type exp = raw_exp Loc.t
  and raw_exp
    = Star
    | Set of int
    | Arr of exp * exp
    | SArr of exp * exp
    | Box of exp * exp
    | ABox of exp * exp
    | Fn of name list * exp
    | Lam of name list * exp
    | App of exp * exp
    | AppL of exp * exp
    | Hole of name option
    | Ident of name
    | BVar of int
    | Clos of exp * exp
    | Empty
    | Shift of int
    | Comma of exp * exp
    | Semicolon of exp * exp
    | Nil
    | Annot of exp * exp
    | Ctx of schema

  and schema
    = Schema of (name * exp) list * (name * exp) list

  type pat =
    | PIdent of name
    | Inacc of exp
    | PLam of string list * pat
    | PPar of name
    | PConst of name * pat list
    | PClos of name * exp
    | PEmpty
    | PShift of int
    | PDot of pat * pat
    | PNil
    | PComma of pat * name option * pat
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
    | Codata of name * params * exp * decls
    | Spec of (name * exp * decls) list
    | DefPM of (name * exp * def_decls) list
    | Def of name * exp * exp
end

module Apx = struct
  open Name

  type index = int
  type universe = int

  type exp
    = Set of universe
    | Star (* Universe of syntax *)
    | Pi of tel * exp  (* A pi type *)
    | SPi of stel * exp (* A syntactic type *)
    | Box of exp * exp
    | Ctx of schema
    | Const of def_name (* The name of a constant *)
    | Var of name
    | Fn of name list * exp
    | App of exp * exp list
    | Lam of string list * exp
    | AppL of exp * exp list
    | BVar of index
    | Clos of exp * exp
    | Empty
    | Shift of int
    | Dot of exp * exp
    | Snoc of exp * string * exp
    | Nil
    | Annot of exp * exp
    | Hole of name

  and schema_part = (string * exp) list
  and schema
    = Schema of schema_part * schema_part

  and tel_entry = icit * name * exp
  and tel = tel_entry list

  and stel_entry = icit * string * exp
  and stel = stel_entry list

  type pat =
    | PVar of name
    | PBVar of index
    | Inacc of exp
    | PLam of string list * pat
    | PConst of def_name * pat list
    | PClos of name * pat_subst
    | SInacc of exp * pat_subst
    | PEmpty
    | PShift of int
    | PDot of pat * pat
    | PNil
    | PSnoc of pat * string * pat
    | PPar of name
    | PUnder
    | PWildcard

  type pats = pat list
  (* name of the constructed type, the type parameters, and the indices *)
  type dsig = def_name * exp list
  type decl = (def_name * tel * dsig)
  type decls = decl list
  type sdecl = (def_name * stel * dsig)
  type sdecls = sdecl list
  (* name is variable referring to term being eliminated... Might not be usable. *)
  type codsig = name * def_name * exp list
  type codecl = def_name * tel * codsig * exp
  type codecls = codecl list
  type rhs
    = Just of exp
    | Impossible of name
  type pat_decls = (pats * rhs) list

  type program =
    (* name, parameters, indices, universe *)
    | Data of def_name * tel * tel * universe * decls
    | Codata of def_name * tel * tel * universe * codecls
    | Spec of (def_name * stel * sdecls) list
    | DefPM of (def_name * tel * exp * pat_decls) list
    | Def of def_name * exp * exp
end

module Int = struct
  open Name

  type index = int
  type universe = int

  type exp
    = Set of universe
    | Pi of tel * exp  (* A pi type *)
    | Box of bctx * syn_exp
    | Ctx of schema
    | Const of def_name (* The name of a constant *)
    | Var of name
    | Fn of name list * exp
    | App of exp * exp list
    | BCtx of bctx
    | Annot of exp * exp
    | Hole of name
    | TermBox of bctx * syn_exp

  and syn_exp
    = Lam of (string * syn_exp) list * syn_exp
    | AppL of syn_exp * syn_exp list
    | SConst of def_name (* The name of a syntactic constant *)
    | BVar of index
    | Clos of syn_exp * syn_exp * bctx
    | Empty
    | Dot of syn_exp * syn_exp
    | Comp of syn_exp * bctx * syn_exp
    | Shift of int
    | ShiftS of int * syn_exp
    | Star (* Universe of syntax *)
    | SPi of stel * syn_exp (* A syntactic type *)
    | SBCtx of bctx
    | SCtx of schema
    | Unbox of exp * syn_exp * bctx

  and schema_part = (string * syn_exp) list
  and schema
    = Schema of schema_part * schema_part

  and bctx
    = Nil
    | CtxVar of name
    | Snoc of bctx * string * syn_exp

  and tel_entry = icit * name * exp
  and tel = tel_entry list

  and stel_entry = icit * string * syn_exp
  and stel = stel_entry list

  type ctx = (name * exp) list

  let id_sub = Shift 0

  type pat =
    | PVar of name
    | Inacc of exp
    | PConst of def_name * pat list
    | PBCtx of pat_bctx
    | PUnder
    | PTBox of bctx * syn_pat

  and syn_pat =
    | PBVar of index
    | PPar of name
    | PLam of (string * syn_exp) list * syn_pat
    | PSConst of def_name * syn_pat list
    | PUnbox of name * pat_subst * bctx
    | SInacc of exp * pat_subst * bctx
    | PEmpty
    | PShift of int
    | PDot of syn_pat * syn_pat

  and pat_bctx =
    | PNil
    | PSnoc of pat_bctx * string * syn_exp
    | PCtxVar of name

  type pats = pat list
  type syn_pats = syn_pat list
  (* name of the constructed type, the type parameters, and the indices *)
  type dsig = def_name * exp list
  type spec_dsig = def_name * syn_exp list

  type decl = (def_name * tel * dsig)
  type decls = decl list
  type sdecl = (def_name * stel * spec_dsig)
  type sdecls = sdecl list

  type codsig = name * def_name * exp list
  type codecl = def_name * tel * codsig * exp
  type codecls = codecl list

  type single_subst = name * exp
  type subst = single_subst list

  type rhs
    = Just of exp
    | Impossible of name

  type split_tree
    = Node of ctx * pats * exp * name * split_tree list
    | Incomplete of ctx * pats * exp
    | Leaf of ctx * pats * exp * rhs

  type pat_decls = (pats * rhs) list

  type program =
    (* name, parameters, indices, universe *)
    | Data of def_name * tel * tel * universe * decls
    | Codata of def_name * tel * tel * universe * codecls
    | Spec of (def_name * stel * sdecls) list
    | DefPM of (def_name * tel * exp * pat_decls) list
    | DefPMTree of (def_name * exp * split_tree) list
    | Def of def_name * exp * exp

  (* Some conversions on internal syntax  *)

  let exp_list_of_tel tel = List.map (fun (_, _, s) -> s) tel

  let rec syn_exp_of_pat_subst : pat_subst -> syn_exp = function
    | CShift n -> Shift n
    | CEmpty -> Empty
    | CDot (s, i) -> Dot(syn_exp_of_pat_subst s, BVar i)

  let rec exp_of_pat : pat -> exp =
    fun p -> match p with
             | PVar n -> Var n
             | Inacc e -> e
             | PConst (n, ps) ->
                App (Const n, List.map (exp_of_pat) ps)

             | PTBox (cP, p) ->
                TermBox(cP, syn_exp_of_pat p)

             | PBCtx cP -> BCtx (bctx_of_pat_ctx cP)
             | PUnder -> raise (Error.Violation "We'd be very surprised if this were to happen.")

  and syn_exp_of_pat =
    function
    | PBVar i -> BVar i
    | PPar n -> Unbox(Var n, id_sub, Nil) (* MMMM *)

    | PLam (fs, p) -> Lam (fs, syn_exp_of_pat p)
    | PSConst (n, ps) ->
       AppL (SConst n, List.map (syn_exp_of_pat) ps)
    | PUnbox (n, s, cP) -> Unbox (Var n, syn_exp_of_pat_subst s, cP)
    | SInacc (e, s, cP) -> Unbox (e, syn_exp_of_pat_subst s, cP)
    | PEmpty -> Empty
    | PShift i -> Shift i
    | PDot (p1, p2) -> Dot (syn_exp_of_pat p1, syn_exp_of_pat p2)

  and bctx_of_pat_ctx = function
    | PNil -> Nil
    | PSnoc (cP, x, t) -> Snoc (bctx_of_pat_ctx cP, x, t)
    | PCtxVar n -> CtxVar n

end

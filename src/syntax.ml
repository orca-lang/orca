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

  type exp = raw_exp Location.t
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
     | EmptyS
     | Shift of int
     | Comma of exp * exp
     | Semicolon of exp * exp
     | Nil
     | Annot of exp * exp
     | Ctx

  type pat =
    | PIdent of name
    | Innac of exp
    | PLam of string list * pat
    | PPar of name
    | PConst of name * pat list
    | PClos of name * exp
    | PEmptyS
    | PShift of int
    | PDot of pat * pat
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
    | Codata of name * params * exp * decls
    | Syn of name * exp * decls
    | DefPM of name * exp * def_decls
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
    | Ctx (* of exp *) (* Let's think about it *)
    | Const of def_name (* The name of a constant *)
    | Dest of def_name
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
    | Snoc of exp * string * exp
    | Nil
    | Annot of exp * exp
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
    | PClos of name * pat_subst
    | SInnac of exp * pat_subst
    | PEmptyS
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
  type codecls = (def_name * tel * dsig * exp) list
  type rhs
    = Just of exp
    | Impossible of name
  type pat_decls = (pats * rhs) list

  type program =
    (* name, parameters, indices, universe *)
    | Data of def_name * tel * tel * universe * decls
    | Codata of def_name * tel * tel * universe * codecls
    | Syn of def_name * stel * sdecls
    | DefPM of def_name * tel * exp * pat_decls
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
    | Ctx (* of exp *) (* Let's think about it *)
    | Const of def_name (* The name of a constant *)
    | Dest of def_name
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
    | SCtx
    | Unbox of exp * syn_exp * bctx

  and bctx
    = Nil
    | CtxVar of name
    | Snoc of bctx * string * syn_exp

   and tel_entry = icit * name * exp
   and tel = tel_entry list

   and stel_entry = icit * string * syn_exp
   and stel = stel_entry list

  let id_sub = Shift 0

  type pat =
    | PVar of name
    | Innac of exp
    | PConst of def_name * pat list
    | PBCtx of pat_bctx
    | PPar of name
    | PUnder
    | PWildcard
    | PTBox of bctx * syn_pat

  and syn_pat =
    | PBVar of index
    | PLam of (string * syn_exp) list * syn_pat
    | PSConst of def_name * syn_pat list
    | PUnbox of name * pat_subst * bctx
    | SInnac of exp * pat_subst * bctx
    | PEmpty
    | PShift of int
    | PDot of syn_pat * syn_pat

  and pat_bctx =
    | PNil
    | PSnoc of pat_bctx * string * syn_pat
    | PCtxVar of name

  type pats = pat list
  type syn_pats = syn_pat list
  (* name of the constructed type, the type parameters, and the indices *)
  type dsig = def_name * exp list
  type syn_dsig = def_name * syn_exp list

  type decl = (def_name * tel * dsig)
  type decls = decl list
  type sdecl = (def_name * stel * syn_dsig)
  type sdecls = sdecl list

  type codecls = (def_name * tel * dsig * exp) list
  type rhs
    = Just of exp
    | Impossible of name
  type pat_decls = (pats * rhs) list

  type program =
    (* name, parameters, indices, universe *)
    | Data of def_name * tel * tel * universe * decls
    | Codata of def_name * tel * tel * universe * codecls
    | Syn of def_name * stel * sdecls
    | DefPM of def_name * tel * exp * pat_decls
    | Def of def_name * exp * exp
end

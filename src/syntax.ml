type icit = Explicit | Implicit
type def_name = string

type pat_subst
  = CShift of int
  | CEmpty
  | CDot of pat_subst * int

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
    | Star (* Universe of syntax *)
    | Pi of tel * exp  (* A pi type *)
    | SPi of stel * exp (* A syntactic type *)
    | Box of bctx * exp
    | TermBox of bctx * exp
    | Ctx (* of exp *) (* Let's think about it *)
    | Const of def_name (* The name of a constant *)
    | Dest of def_name
    | Var of name
    | Fn of name list * exp
    | App of exp * exp list
    | Lam of (string * exp) list * exp
    | AppL of exp * exp list
    | BVar of index
    | Clos of exp * exp * bctx
    | BCtx of bctx
    | Annot of exp * exp
    | Hole of name
    | Empty
    | Dot of exp * exp
    | Comp of exp * bctx * exp
    | Shift of int
    | ShiftS of int * exp


  and bctx
    = Nil
    | CtxVar of name
    | Snoc of bctx * string * exp

   and tel_entry = icit * name * exp
   and tel = tel_entry list

   and stel_entry = icit * string * exp
   and stel = stel_entry list

  let idSub = Shift 0

  type pat =
    | PVar of name
    | PBVar of index
    | Innac of exp
    | PLam of (string * exp) list * pat
    | PConst of def_name * pat list
    | PClos of name * pat_subst * bctx
    | PBCtx of pat_bctx
    | PEmpty
    | PShift of int
    | PDot of pat * pat
    | PPar of name
    | PUnder
    | PWildcard

  and pat_bctx =
    | PNil
    | PSnoc of pat_bctx * string * pat
    | PCtxVar of name

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


module Ext = struct

  type name = string

  type pats = name list

  type exp =
    | Star
    | Set of int
    | Pi of name * exp * exp
    | Box of exp * exp
    | Fn of name * exp
    | Lam of name * exp
    | App of exp * exp
    | AppL of exp * exp
    | Ident of name
    | Clos of exp * exp
    | EmptyS
    | Shift of int
    | Comma of exp * exp
    | Nil
    | Annot of exp * exp

  type decls = (name * exp) list
  type def_decls = (pats * exp) list
  type icit = Explicit | Implicit
  type param = icit * name * exp
  type params = param list

  type program =
    | Data of name * params * exp * decls
    | Syn of name * params * exp * decls
    | DefPM of name * exp * def_decls
    | Def of name * exp * exp
end

type name = string

type pats = name list

type exp =
| Star
| Set of int
| Arr of exp * exp
| Box of ctx * exp
| Fn of name * exp
| Lam of name * exp
| App of exp * exp list
| AppL of exp * exp

and ctx =
| Nil
| Cons of ctx * exp
    
type decls = (name * exp) list
type def_decls = (pats * exp) list
type param = ParamI of name * exp | ParamE of name * exp
type params = param list
  
type program =
| Data of name * params * exp * decls
| Syn of name * params * exp * decls
| DefPM of name * exp * def_decls
| Def of name * exp * exp

open Rlist

type icit = Explicit | Implicit
type def_name = string

type index = int * (int option)



let inc_idx (n, p) = (n + 1, p)
let dec_idx (n, p) = (n - 1, p)
let shift_idx (n, p) m = (n + m , p)

let zidx = (0, None)

type pat_subst
  = CShift of int
  | CEmpty
  | CDot of pat_subst * index

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
    | Block of (name * exp) rlist

  and schema
    = Schema of (name * exp) list * (name * exp) list (* quant, block *)

  type pat =
    | PIdent of name
    | Inacc of exp
    | PLam of string list * pat
    | PPar of name * int option
    | PConst of name * pat list
    | PClos of name * exp
    | PEmpty
    | PShift of int
    | PDot of pat * pat
    | PNil
    | PComma of pat * name option * pat
    | PCommaBlock of pat * name list
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
    | Block of (string * exp) rlist
    | TBlock of exp rlist

  and schema_part = (string * exp) list 
  and schema
    = Schema of schema_part * schema_part (* quant, block *)

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
    | PPar of name * int option
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
    | Empty
    | Dot of syn_exp * syn_exp
    | Shift of int
    | Star (* Universe of syntax *)
    | SPi of stel * syn_exp (* A syntactic type *)
    | Block of (string * syn_exp) rlist
    | TBlock of syn_exp rlist
    | SBCtx of bctx
    | SCtx of schema
    | Unbox of exp * syn_exp
    | UnboxParam of name * int * syn_exp

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
  let i0 = BVar(0, None)

  type pat =
    | PVar of name
    | Inacc of exp
    | PConst of def_name * pat list
    | PBCtx of pat_bctx
    | PUnder
    | PTBox of bctx * syn_pat

  and syn_pat =
    | PBVar of index
    | PPar of name * int option
    | PLam of (string * syn_exp) list * syn_pat
    | PSConst of def_name * syn_pat list
    | PUnbox of name * pat_subst
    | SInacc of exp * pat_subst
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


type reducible
  = Reduces
  | Stuck

type signature_entry
  = Definition of def_name * tel * exp * exp * reducible (* the name, the type, and the definition *)
  (* name, parameters, constructed type *)
  | Constructor of def_name * tel * dsig
  (* name, indices, type of codata type being eliminated, resulting type *)
  | Observation of def_name * tel * codsig * exp
  | SConstructor of def_name * stel * spec_dsig
  (* name, parameters, indices, resulting universe *)
  | DataDef of def_name * tel * tel * universe
  | CodataDef of def_name * tel * tel * universe
  | SpecDef of def_name * stel
  | Program of def_name * tel * exp * pat_decls * reducible
  | PSplit of def_name * exp * split_tree option

type signature = signature_entry list

let signature_entry_name = function
    | Definition (n', _, _, _, _)
    | Program (n', _, _, _, _)
    | PSplit (n', _, _)
    | DataDef (n', _, _, _)
    | CodataDef (n', _, _, _)
    | SpecDef (n', _)
    | SConstructor (n', _, _)
    | Observation (n', _, _, _)
    | Constructor (n', _, _) -> n'
    
let rec lookup_sign_entry (sign : signature) (n : def_name) : signature_entry =
  let el en = signature_entry_name en = n
  in
    try
      List.find el sign
    with Not_found ->
      raise (Error.Violation ("Unable to find " ^ n ^ " in the signature"))


let is_syn_con (sign : signature) (n : def_name) =
  match lookup_sign_entry sign n with
  | SConstructor _ -> true
  | _ -> false

let lookup_params (sign : signature) (n : def_name) : tel =
  match lookup_sign_entry sign n with
  | DataDef (_, tel, _, _)
  | CodataDef (_, tel, _, _) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " needs to be (co)data type declaration"))

let lookup_syn_def (sign : signature) (n : def_name) : stel =
  match lookup_sign_entry sign n with
  | SpecDef (_, tel) -> tel
  | _ -> raise (Error.Error ("Constant " ^ n ^ " not a syntactic type"))

let lookup_cons_entry (sign : signature) (c : def_name) : tel * dsig =
  match lookup_sign_entry sign c with
  | Constructor (_, tel, dsig) -> tel, dsig
  | _ -> raise (Error.Error ("Constant " ^ c ^ " was expected to be a constructor."))

type lookup_result
  = D of exp                    (* A definition without pattern matching *)
  | P of pat_decls              (* A definition with pattern matching *)
  | N                           (* A non-reducible constant *)
  | S of split_tree             (* A definition with pattern matching (using split tree) *)

let lookup_sign_def sign n =
  match lookup_sign_entry sign n with
  | Definition (_, _, _, _, Stuck) -> N (* if it is stuck it does not reduce *)
  | Definition (_, _, _, e, _) -> D e
  | Constructor _ -> N
  | DataDef _ -> N
  | CodataDef _ -> N
  | SConstructor _ -> N
  | SpecDef _ -> N
  | Program (_, _, _, _, Stuck) -> N (* if it is stuck it does not reduce *)
  | Program (_, _, _, ds, _) -> P ds
  | PSplit (_, _, None) -> N (* if it is stuck it does not reduce *)
  | PSplit (_, _, Some split) -> S split
  | Observation _ -> raise (Error.Violation "Observation not implemented")

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
    | PPar (n, None) -> Unbox(Var n, id_sub) (* MMMM *)
    | PPar (n, Some pr) -> UnboxParam(n, pr, id_sub) (* MMMM *)
    | PLam (fs, p) -> Lam (fs, syn_exp_of_pat p)
    | PSConst (n, ps) ->
       AppL (SConst n, List.map (syn_exp_of_pat) ps)
    | PUnbox (n, s) -> Unbox (Var n, syn_exp_of_pat_subst s)
    | SInacc (e, s) -> Unbox (e, syn_exp_of_pat_subst s)
    | PEmpty -> Empty
    | PShift i -> Shift i
    | PDot (p1, p2) -> Dot (syn_exp_of_pat p1, syn_exp_of_pat p2)

  and bctx_of_pat_ctx = function
    | PNil -> Nil
    | PSnoc (cP, x, t) -> Snoc (bctx_of_pat_ctx cP, x, t)
    | PCtxVar n -> CtxVar n

end

open Name
open Syntax
open Print
open Sign
open Meta
module A = Syntax.Apx
module I = Syntax.Int
module AP = Print.Apx
module IP = Print.Int

type pat =
  | PVar of name
  | PBVar of int
  | UInac of A.exp              (* those are user written inacessible patterns *)
  | IInac of I.exp              (* those are inferred inacessible patterns from index unification *)
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

let rec print_pat (p : pat) : string = match p with
  | PVar n -> print_name n
  | PPar n -> "(<: " ^ print_name n ^ ")"
  | PBVar i -> "i" ^ string_of_int i
  | UInac e -> "." ^ AP.print_exp e
  | IInac e -> "+" ^ IP.print_exp e
  | PLam (fs, p) -> "(\ " ^ String.concat " "  fs ^ " " ^ print_pat p ^ ")"
  | PConst (n, ps) -> "(" ^ n ^ " " ^ print_pats ps ^ ")"
  | PClos (n, s) -> print_name n ^ "[" ^ print_pat_subst s ^ "]"
  | PEmptyS -> "^"
  | PShift i -> "^ " ^ string_of_int i
  | PDot (p1, p2) -> "(" ^ print_pat p1 ^ " ; " ^ print_pat p2 ^ ")"
  | PNil -> "0"
  | PSnoc (p1, x, p2) -> "(" ^ print_pat p1 ^ " , " ^ x ^ ":" ^ print_pat p1 ^ ")"
  | PUnder -> "_"
  | PWildcard -> "._"
and print_pats ps = String.concat " " (List.map (fun p -> "(" ^ print_pat p ^ ")") ps)

let rec exp_of_pat_subst : pat_subst -> I.exp = function
  | CShift n -> I.Shift n
  | CEmpty -> I.EmptyS
  | CDot (s, i) -> I.Dot(exp_of_pat_subst s, I.BVar i)

let rec exp_of_pat : pat -> I.exp = function
  | PVar n -> I.Var n
  | PPar n -> I.Var n           (* MMMMM *)
  | PBVar i -> I.BVar i
  | IInac e -> e
  | UInac e -> raise (Error.Violation "We hope to never see you again (this message, not the user)")
  | PLam (fs, p) -> I.Lam (fs, exp_of_pat p)
  | PConst (n, ps) -> I.App (I.Const n, List.map exp_of_pat ps)
  | PClos (n, s) -> I.Clos (I.Var n, exp_of_pat_subst s)
  | PEmptyS -> I.EmptyS
  | PShift i -> I.Shift i
  | PDot (p1, p2) -> I.Dot (exp_of_pat p1, exp_of_pat p2)
  | PNil -> I.Nil
  | PSnoc (p1, x, p2) -> I.Snoc (exp_of_pat p1, x, exp_of_pat p2)
  | PUnder -> raise (Error.Violation "We'd be very surprised if this were to happen.")
  | PWildcard -> raise (Error.Violation "We'd also be very surprised if this were to happen.")

let pvar_list_of_ctx : ctx -> pat list = List.map (fun (x, _) -> PVar x)

type single_psubst = name * pat
type psubst = single_psubst list

let print_psubst c = "[" ^ (String.concat "," (List.map (fun (x, e) -> print_name x ^ " := " ^ print_pat e) c)) ^ "]"

let rec psubst ((x, p') as s) (p : pat) :  pat =
  match p with
  | PVar n when n = x -> p'
  | PVar n -> PVar n
  | PPar n when n = x -> p'   (* MMMMM *)
  | PPar n -> PPar n
  | PBVar i -> PBVar i
  | IInac e -> IInac (subst (x, exp_of_pat p') e)
  | UInac e -> raise (Error.Violation "We hope to never see you again (this message, not the user)")
  | PLam (f, p) -> PLam(f, psubst s p)
  | PConst (n, ps) -> PConst(n, List.map (psubst s) ps)
  | PClos (n, s) when n = x ->
     begin match p' with
     | PVar n' -> PClos (n', s)
     | _ -> assert false (* MMMMMMM *)
     end
  | PClos (n, s) -> PClos (n, s)
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

let psubst_of_ctx : ctx -> psubst = List.map (fun (x, _) -> x, PVar x)

let simul_psubst_on_ctx sigma =
    List.map (fun (x, e) -> x, simul_psubst sigma e)

let rec rename_ctx_using_psubst (cG : ctx) (sigma : psubst) =
  match cG with
  | [] -> []
  | (x, t) :: cG' ->
     match lookup_ctx sigma x with
     | Some (PVar y) -> (y, t) :: (rename_ctx_using_psubst cG' sigma)
     | _ -> (x, t) :: (rename_ctx_using_psubst cG' sigma)


let shift_psubst_by_ctx sigma cG =
  let sigma' = sigma @ (List.map (fun (x, _) -> x, PVar x) cG) in
  Debug.print (fun () -> "Shift called with sigma = " ^ print_psubst sigma
                         ^ "\ncG = " ^ print_ctx cG
                         ^ "\nresulting in " ^ print_psubst sigma'
                         ^ ".");
  sigma'


let rec proc_pats (p : A.pats) : pats = List.map proc_pat p
and proc_pat : A.pat -> pat = function
  | A.PVar n -> PVar n
  | A.PBVar n -> PBVar n
  | A.Innac e -> UInac e
  | A.PLam (xs, p) -> PLam (xs, proc_pat p)
  | A.PConst (n, ps) -> PConst (n, proc_pats ps)
  | A.PClos (n, s) -> PClos (n, s)
  | A.PEmptyS -> PEmptyS
  | A.PShift i -> PShift i
  | A.PDot (p1, p2) -> PDot (proc_pat p1, proc_pat p2)
  | A.PNil -> PNil
  | A.PSnoc (g, x, p) -> PSnoc (proc_pat g, x, proc_pat p)
  | A.PPar x -> PPar x
  | A.PUnder -> PUnder
  | A.PWildcard -> PWildcard

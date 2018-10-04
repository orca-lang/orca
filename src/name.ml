(* Unique name generation module *)

(* The original name * a unique int * a flag for free names *)
type name = string * int * bool

let gen_sym =
  let state = ref 0 in
  fun () -> state := !state + 1 ; !state - 1

let gen_name s = (s, gen_sym (), false)

(* A floating name is one that is not used in a term *)
let gen_floating_name () = ("@", gen_sym(), true)

let refresh_name (s, _, fl) = (s, gen_sym(), fl)

let print_name = function
  | n, i, false -> n ^ "_" ^ string_of_int i
  | _, i, true -> "@" ^ string_of_int i

let print_names ns = "(" ^ (String.concat ", " (List.map print_name ns)) ^ ")"

let print_names_no_comma ns = "(" ^ (String.concat " " (List.map print_name ns)) ^ ")"

let is_name_floating (_, _, x) = x

let fmt_name pps (s, n, b) =
  (*if b
  then Format.fprintf pps "_%s%d_" s n
  else *)Format.fprintf pps "%s!!%d" s n

let disable_beautify, do_beautify =
  let beau = ref true in
  (fun () -> beau := false),
  (fun () -> !beau)

(* Counts the number of times a given name appears in a context *)
let rec count (s,_,_ as n : name) : (name * 'a) list -> int = function
  | [] -> 0
  | ((s', _, _), _) :: cG' when s' = s -> 1 + count n cG'
  | _ :: cG' -> count n cG'

(* Beautify a name that appears in the context *)
let rec beautify_name (s, _, _ as n) cG =
  if not (do_beautify ()) then None
  else match cG with
  | [] -> None
  | (n', _)::cG when n = n' ->
     let c = count n cG in
     if c = 0 then
       Some s
     else
       Some (s ^ "_" ^ string_of_int c)
  | (n', _)::cG -> beautify_name n cG

(* Beautify a new name for the context *)
let rec beautify_new_name (s, _, _ as n) cG =
  if not (do_beautify ()) then None
  else let c = count n cG in
       if c = 0 then
         Some s
       else
         Some (s ^ "_" ^ string_of_int c)

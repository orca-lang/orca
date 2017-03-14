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

let print_name (n, i, _) = n ^ "_" ^ string_of_int i

let print_names ns = "(" ^ (String.concat ", " (List.map print_name ns)) ^ ")"

let is_name_floating (_, _, x) = x

let fmt_name pps (s, n, b) =
  if b
  then Format.printf "_%s_%d_" s n
  else Format.printf "%s_%d" s n

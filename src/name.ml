(* Unique name generation module *)

type name = string * int

let gen_sym =
  let state = ref 0 in
  fun () -> state := !state + 1 ; !state - 1


let gen_name s = (s, gen_sym ())

let refresh_name (s, _) = (s, gen_sym())

let print_name (n, i) = n ^ "_" ^ string_of_int i

(* This file contains general utilities *)

(* Concatenante the string s with itself n times *)

let rec concat_n_times n s =
  match n with
  | 0 -> ""
  | n -> s ^ concat_n_times (n-1) s

let empty_list = function
  | [] -> true
  | _ -> false

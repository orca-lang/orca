(* This file contains general utilities *)

(* Concatenante the string s with itself n times *)
let rec concat_n_times n s =
  match n with
  | 0 -> ""
  | n -> s ^ concat_n_times (n-1) s

(* Remove n from list l *)
let (--) l n = List.filter ((<>) n) l

let rec unique : 'a list -> 'a list = function
  | [] -> []
  | x::xs -> x::unique (xs -- x)

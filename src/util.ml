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

(* Splits the list in the n first and the rest *)
let split_first n l =
  let rec split n l' =
    match n, l' with
    | 0, l' -> [], l'
    | n, x::xs ->
       let l1, l2 = split (n-1) xs in
       x::l1, l2
    | _ -> raise (Error.Violation ("split_first called with " ^ string_of_int n
                                   ^ " and a list of only length " ^ string_of_int (List.length l)))
  in
  split n l

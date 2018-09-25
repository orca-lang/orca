(* Utility functions *)

val concat_n_times : int -> string -> string

val ( -- ) : 'a list -> 'a -> 'a list

val unique : 'a list -> 'a list

val split_first : int -> 'a list -> 'a list * 'a list

val diff : 'a list -> 'a list -> 'a list
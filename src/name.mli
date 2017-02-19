(* Unique name generation module *)

type name

val gen_name : string -> name

val refresh_name : name -> name

val print_name : name -> string

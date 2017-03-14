(* Unique name generation module *)

type name

val gen_name : string -> name

val gen_floating_name : unit -> name

val refresh_name : name -> name

val print_name : name -> string

val print_names : name list -> string

val is_name_floating : name -> bool

val fmt_name : Format.formatter -> name -> unit

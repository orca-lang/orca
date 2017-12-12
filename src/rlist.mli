(* Lists that cons to the right *)


type 'a rlist = RNil | RCons of 'a rlist * 'a
val from_list : 'a list -> 'a rlist
val to_list : 'a rlist -> 'a list
val to_string : ?sep:string -> ('a -> string) -> 'a rlist -> string
val nth: 'a rlist -> int -> 'a
val map : ('a -> 'b) -> 'a rlist -> 'b rlist
val mapl : ('a -> 'b) -> 'a rlist -> 'b list
val fold : ('a -> 'b -> 'a) -> 'a -> 'b rlist -> 'a
val fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b rlist -> 'c rlist -> 'a

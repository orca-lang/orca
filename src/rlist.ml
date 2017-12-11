(* Lists that cons to the right *)

type 'a rlist = RNil | RCons of 'a rlist * 'a

let rec from_list l = List.fold_right (fun e l -> RCons (l, e)) l RNil

let rec fold f acc = function
  | RNil -> acc
  | RCons (l, e) -> fold f (f acc e) l

let rec map f = function
  | RNil -> RNil
  | RCons (l, e) -> RCons(map f l, f e)


let rec nth l i = match l with
  | RNil -> raise Not_found
  | RCons (_, e) when i = 0 -> e
  | RCons (l, _) -> nth l (i-1)


let rec to_string ?(sep = ", ") f l = fold (fun l e -> l ^ sep ^ f e) "" l

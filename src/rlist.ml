(* Lists that cons to the right *)

type 'a rlist = RNil | RCons of 'a rlist * 'a

let rev l = 
  let rec rev acc = function 
    | RNil -> acc
    | RCons (l, e) -> rev (RCons (acc, e)) l
  in rev RNil l 

let rec fold f acc = function
  | RNil -> acc
  | RCons (l, e) -> fold f (f acc e) l

let rec from_list l = List.fold_right (fun e l -> RCons (l, e)) l RNil

let rec to_list l = List.rev (fold (fun acc e -> e::acc) [] l)

let rec fold2 f acc l1 l2 = match l1, l2 with
  | RNil, RNil -> acc
  | RCons (l1, e1), RCons(l2, e2) -> fold2 f (f acc e1 e2) l1 l2
  | _ -> raise (Invalid_argument "fold2 called with lists of different length")


let rec map f = function
  | RNil -> RNil
  | RCons (l, e) -> RCons(map f l, f e)


let rec mapl f = function
  | RNil -> []
  | RCons (l, e) -> f e::mapl f l


let rec nth l i = match l with
  | RNil -> raise Not_found
  | RCons (_, e) when i = 0 -> e
  | RCons (l, _) -> nth l (i-1)


let rec to_string ?(sep = ", ") f l = fold (fun l e -> f e ^ sep ^ l) "" l

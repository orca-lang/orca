type coords = {
  startpos: Lexing.position;
  endpos: Lexing.position;
  }

type src_pos = coords option

type 'a t = P of src_pos * 'a

let make startpos endpos content =
  P (Some {startpos = startpos;  endpos = endpos}
    , content)


let make_from l1 l2 content = match l1, l2 with
| P(Some s, _), P(Some e, _) -> P(Some {startpos = s.startpos ;
		       endpos = e.endpos },
		       content = content )
| _ , _ -> P(None, content)

let ghost content = P(None, content)

let content (P(_, content)) = content
let loc (P(pos, _ )) = pos

let copy (P(l,_)) content = P (l, content)

let string_of_position = function Some p ->
  let pos1 = p.startpos in
  let pos2 = p.endpos in
  (* let file = pos1.Lexing.pos_fname in *)
  let line = pos1.Lexing.pos_lnum in
  let char1 = pos1.Lexing.pos_cnum - pos1.Lexing.pos_bol in
  let char2 = pos2.Lexing.pos_cnum - pos1.Lexing.pos_bol in (* intentionally [pos1.pos_bol] *)
  Printf.sprintf "line %d, characters %d-%d" line (char1 + 1) (char2 + 1)
  | None -> "Unknown location"

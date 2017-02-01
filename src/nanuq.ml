
module Menhir = MenhirLib.Convert.Simplified

exception Syntax_error of Lexing.position
exception Scanning_error of Lexing.position * string

let file_name = "nanuq"

let parse menhir_parser lexbuf =
  let position = ref (Lexer.initial_pos file_name) in
  let lexer () =
    let ante_position = !position in
    let post_position, token = Lexer.main_scanner !position lexbuf in
    let () = position := post_position in (* Lexing.({!position with pos_lnum = !position.pos_lnum + nlines;}) in *)
    (token, ante_position, post_position) in
  let revised_parser = Menhir.traditional2revised menhir_parser
  in try
       revised_parser lexer
    with
      | Lexer.Error x -> raise (Scanning_error (!position, x))
      | Parser.Error  -> raise (Syntax_error !position)

let usage_msg = "Bears ahead"
let file = ref ""
let args = []

let () =
  try
    Arg.parse args (fun s -> file := s) usage_msg;
    let ch = if !file = "" then stdin else open_in !file in
    let lexbuf = Ulexing.from_utf8_channel ch in
    (* let c = String.concat "\n" *)
    (*    (List.map (fun x -> Syntax.Int.print_program (snd (Preproc.pre_process [] [] x))) (parse Parser.program lexbuf)) *)
    let c = String.concat "\n"
                          (List.map Syntax.Int.print_program (snd
                                                       (List.fold_left (fun (s, ds) d -> let s', d' = Preproc.pre_process s d in s', (d' :: ds)) ([], []) (parse Parser.program lexbuf))))
    in

    print_string ("The tree is:\n" ^ c ^ "\n")
  with
  | Syntax_error pos -> Printf.printf "Syntax error in line %d, col %d\n" pos.Lexing.pos_lnum pos.Lexing.pos_cnum
  | Scanning_error (pos, s) ->
    Printf.printf "Scanning error in line %d, col %d\nMessage:%s\n"
      pos.Lexing.pos_lnum pos.Lexing.pos_cnum s
  | Ulexing.Error -> Printf.printf "Ulexing Error\n"

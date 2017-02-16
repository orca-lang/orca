
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


let set_print_external, get_print_external =
  let print = ref false in
  (fun () -> print := true),
  (fun () -> !print)

let set_run_tc, get_run_tc =
  let print = ref false in
  (fun () -> print := true),
  (fun () -> !print)


let usage_msg = "Bears ahead"
let file = ref ""
let args = [("-ext", Arg.Unit set_print_external, "Print external syntax before preprocessing.")
           ;("-tc", Arg.Unit set_run_tc, "Run the incomplete typechecker.")
           ;("-debug", Arg.Unit Debug.set_debug_on, "Generates a log file with information about the file that was checked")
           ]

let () =
  try
    Arg.parse args (fun s -> file := s) usage_msg;

    Debug.print (fun () -> "Processing file: " ^ !file) ;
    let ch = if !file = "" then stdin else open_in !file in
    let lexbuf = Ulexing.from_utf8_channel ch in

    let program = parse Parser.program lexbuf in

    Debug.print_string "* The external tree is:";
    Debug.print (fun () -> String.concat "\n"
        (List.rev (List.map Syntax.Ext.print_program program)));

    begin if get_print_external() then
      let ext_pp = String.concat "\n"
        (List.rev (List.map Syntax.Ext.print_program program))
      in
      print_string ("The external tree is:\n" ^ ext_pp ^ "\n")
    end;

    let _, int_rep = List.fold_left
                           (fun (s, ds) d -> let s', d' = Preproc.pre_process s d in s', (d' :: ds))
                           ([], [])
                           program
    in
    let int_rep = List.rev int_rep in (* Because the fold inverts them. TODO consider a right fold? *)

    let int_pp = String.concat "\n"
        (List.rev (List.map Syntax.Int.print_program int_rep))
    in

    print_string ("* The internal tree is:\n" ^ int_pp ^ "\n");
    Debug.print (fun () -> "The internal tree is:\n" ^ int_pp ^ "\n");

    if get_run_tc () then begin
           Debug.print_string "Starting typechecking." ;
            let _sign' = List.fold_left Typecheck.tc_program [] int_rep in
            Debug.print_string "The file was typechecked.";
            print_string "Typechecked."
      end;
  with
  | Syntax_error pos ->
     Debug.print_string "There was a syntax error in the file." ;
     Printf.printf "Syntax error in line %d, col %d.\n" pos.Lexing.pos_lnum pos.Lexing.pos_cnum
  | Scanning_error (pos, s) ->
     Debug.print_string "There was a lexing error in the file." ;
     Printf.printf "Scanning error in line %d, col %d\nMessage:%s\n"
                   pos.Lexing.pos_lnum pos.Lexing.pos_cnum s
  | Ulexing.Error ->
     Debug.print_string "There was a lexing error in the file.(2)" ;
     Printf.printf "Ulexing Error\n"
  | Error.Error msg ->
     Debug.print_string ("An error occured while processing the input:\n" ^ msg) ;
     Printf.printf "An error occured while processing your input.\n\t%s\n" msg
  | Error.Violation msg ->
     Debug.print_string ("An unexpected error occured, report this as a bug.\n" ^ msg);
     Printf.printf "An unexpected error occured, report this as a bug.\n\t%s\n" msg

module Menhir = MenhirLib.Convert.Simplified

open Pretty

let file_name = "orca"
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
      | Lexer.Error x -> raise (Error.Scanning_error (!position, x))
      | Parser.Error  -> raise (Error.Syntax_error !position)


let set_print_external, get_print_external =
  let print = ref false in
  (fun () -> print := true),
  (fun () -> !print)

let set_parse_only, get_parse_only =
  let print = ref false in
  (fun () -> print := true),
  (fun () -> !print)

let disable_ansi, ansi_on =
  let ansi = ref true in
  (fun () -> ansi := false),
  (fun () -> !ansi)

let usage_msg = "Bears ahead"
let file = ref ""
let args = [("-ext", Arg.Unit set_print_external, "Print external syntax before preprocessing.")
           ;("-po", Arg.Unit set_parse_only, "Only parse and preprocess the input (Do not run the typechecker).")
           ;("-debug", Arg.Unit Debug.set_debug_on, "Generates a log file with information about the file that was checked")
           ;("-no-wrapper", Arg.Unit Repl.set_no_wrapper, "Turns off using a read line wrapper.")
           ;("-prompt", Arg.String Repl.set_prompt, "<string> Sets a custom prompt.")
           ;("-verbose", Arg.Unit Debug.set_verbose_on, "Turns on verbose debugging")
           ;("-no-beauty", Arg.Unit Name.disable_beautify, "Turns off beautification in pretty printing")
           ;("-ansi-off", Arg.Unit disable_ansi, "Turns off ansi colours in pretty printing")
           ;("-simple-printer", Arg.Unit Pp.set_simple_pp, "Turns off the fancy pretty printer, and prints S-exps")
           ;("-pm", Arg.Symbol (["old" ; "split" ; "new"], Prog.parse_pm_option)
             ," Select the pattern matching implementation (Default: split).")
           ]

let execute_code (sign : Syntax.Int.signature) (program : Syntax.Ext.program list) : Syntax.Int.signature =
    Debug.print_string "* The external tree is:";
    Debug.print (fun () -> String.concat "\n"
        (List.map Print.Ext.print_program program));

    begin if get_print_external() then
      let ext_pp = String.concat "\n"
        (List.map Print.Ext.print_program program)
      in
      print_string ("The external tree is:\n" ^ ext_pp ^ "\n")
    end;
    let _, apx_rep = List.fold_left
                           (fun (s, ds) d -> let s', d' = Preproc.pre_process s d in s', (d' :: ds))
                           (List.map Syntax.Int.signature_entry_name sign, [])
                           program
    in
    let apx_rep = List.rev apx_rep in (* Because the fold inverts them. TODO consider a right fold? *)

    let apx_pp = String.concat
                   "\n"
                   (List.map Print.Apx.print_program apx_rep)
    in
    Debug.print (fun () -> "The approximate tree is:\n" ^ apx_pp ^ "\n");

    (* print_string apx_pp ; *)       (* TODO : add back the nice pretty printer *)


    if not (get_parse_only ()) then begin
      Debug.print_string "Starting typechecking." ;
      let sign', int_rep = List.fold_left (fun (s, ps) p -> let s', p' = Prog.tc_program s p in s', p'::ps) (sign, []) apx_rep in
      let int_rep = List.rev int_rep in
      if ansi_on() then Fmt.set_style_renderer Fmt.stdout `Ansi_tty;
      Pretty.fmt_programs Fmt.stdout int_rep;

      Debug.print_string "The file was typechecked.";
      print_string "File type-checked successfully.\n";
      sign'
    end
    else
      sign

let parse_fun : Ulexing.lexbuf -> Syntax.Ext.program list =
    parse Parser.program
let () =
  try
    Arg.parse args (fun s -> file := s) usage_msg;

    Debug.print (fun () -> "Processing file: " ^ !file) ;
    if !file = ""
    then Repl.toplevel [] parse_fun execute_code
    else
      begin
        let ch = open_in !file in
        let lexbuf = Ulexing.from_utf8_channel ch in

        let program  : Syntax.Ext.program list = parse_fun lexbuf in
        let _= execute_code [] program in
        ()
      end
  with
  | Error.Syntax_error pos ->
     Debug.print_string "There was a syntax error in the file." ;
     Printf.printf "Syntax error in line %d, col %d.\n" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) ;
     exit 1
  | Error.Scanning_error (pos, s) ->
     Debug.print_string "There was a lexing error in the file." ;
     Printf.printf "Scanning error in line %d, col %d\nMessage:%s\n"
                   pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) s;
     exit 1
  | Ulexing.Error ->
     Debug.print_string "There was a lexing error in the file.(2)" ;
     Printf.printf "Ulexing Error\n";
     exit 1
  | Error.Error_loc (pos, msg) ->
     Debug.print_string ("An error occured while processing the input:\n" ^ msg
                        ^ "\n at position " ^ Loc.string_of_position pos) ;
     Printf.printf "An error occured while processing your input.\n\t%s\nAt %s.\n"
                   msg
                   (Loc.string_of_position pos);
     exit 1

  | Error.Error msg ->
     Debug.print_string ("An error occured while processing the input:\n" ^ msg) ;
     Printf.printf "An error occured while processing your input.\n\t%s\n" msg ;
     exit 1
  | Error.Violation msg ->
     Debug.print_string ("An unexpected error occured, report this as a bug.\n" ^ msg);
     Printf.printf "An unexpected error occured, report this as a bug.\n\t%s\n" msg ;
     exit 1

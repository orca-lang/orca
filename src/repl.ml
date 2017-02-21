open Signature

let prompt_str = ref "🐋 > "

let set_prompt s = prompt_str := s

let set_no_wrapper, get_wrapper =
  let wrap = ref true in
  (fun () -> wrap := false),
  (fun () -> !wrap)

let read_toplevel parser () =
  let ends_with_period str =
    let i = ref (String.length str - 1) in
    while !i >= 0 && List.mem str.[!i] [' '; '\n'; '\t'; '\r'] do decr i done ;
    !i >= 0 && str.[!i] = '.'
  in

  let rec read_more prompt acc =
    if ends_with_period acc
    then acc
    else begin
        print_string prompt ;
        let str = read_line () in
        read_more "  " (acc ^ "\n" ^ str)
      end
  in

  let str = read_more !prompt_str  "" in
  let str = if true || ends_with_period str then Str.first_chars str (String.length str - 1) else str in
  Debug.print (fun () -> "Repl read:" ^ str);
  let lex = Ulexing.from_utf8_string (str ^ "\n") in
  parser lex

let wrapper = ref (Some ["rlwrap"; "ledit"])

(* Attempt to wrap yourself with a line-editing wrapper. *)
let wrap_yourself () =
  if get_wrapper () then
  match !wrapper with
  | None -> ()
  | Some lst ->
     let n = Array.length Sys.argv + 2 in
     let args = Array.make n "" in
     Array.blit Sys.argv 0 args 1 (n - 2);
     args.(n - 1) <- "-no-wrapper";
     List.iter
       (fun wrapper ->
         try
           args.(0) <- wrapper;
           Unix.execvp wrapper args
         with Unix.Unix_error _ -> ())
       lst


let toplevel (sigma : signature) (parser : Ulexing.lexbuf -> Syntax.Ext.program list) exec_cmd =
  let eof = match Sys.os_type with
    | "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "EOF"
  in
  wrap_yourself ();
  print_endline "Welcome to the Orca prototype";
  print_endline ("[Type " ^ eof ^ " to exit.]");
  try
    let sigma = ref sigma in
    Sys.catch_break true ;      (* To catch Ctrl+C and continue with the next command *)
    while true do
      try
        let cmds = read_toplevel parser () in
        Debug.print (fun () -> "About to execute with signature:\n" ^ print_signature !sigma) ;
        sigma := exec_cmd !sigma cmds
      with
      | Error.Error msg -> print_string ("Error:\n" ^ msg ^ "\n")
      | Error.Violation msg -> print_string ("Unexpected error:\n" ^ msg ^ "\nReport this as a bug.\n")

      | Error.Syntax_error pos ->
         let msg = "Syntax error in line " ^  string_of_int pos.Lexing.pos_lnum
                   ^ ", col " ^ string_of_int pos.Lexing.pos_cnum ^ ".\n"
         in
         Debug.print_string ("There was a syntax error." ^ msg) ;
         print_string msg
      | Error.Scanning_error (pos, s) ->
         let msg = "Scanning error in line " ^ string_of_int pos.Lexing.pos_lnum
                         ^ ", col " ^ string_of_int pos.Lexing.pos_cnum
                         ^ "\nMessage:" ^ s
                         ^"\n"
         in
         Debug.print_string ("There was a lexing error in the file." ^ msg ^ "\n") ;
         print_string msg
      | Ulexing.Error ->
         Debug.print_string "There was a lexing error in the file.(2)\n" ;
         print_string "Ulexing Error\n"
      | Sys.Break -> prerr_endline "Interrupted."
    done
  with End_of_file -> ()

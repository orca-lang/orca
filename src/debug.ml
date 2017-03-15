open Printf

let debug_on = ref false
let debug_verbose = ref false
let debug_channel : (out_channel option) ref = ref None
let debug_file_name = "debug.out"
let debug_indent = ref 0
let debug_indent_string = "  "

let in_verbose_sec = ref false

(* Turns debug on and starts a new file *)
let set_debug_on () =
  debug_on := true ;
  debug_channel := Some (open_out debug_file_name)

(* Sets the debug off and closes the open file if any *)
let set_debug_off () =
  debug_on := true ;
  match !debug_channel with
  | None -> ()
  | Some ch -> close_out ch

let set_verbose_on () = set_debug_on (); debug_verbose := true
let set_verbose_off () = set_debug_off (); debug_verbose := false

(* Turns debugging on, but it does not truncate the file *)
let set_debug_cont () =
  debug_on := true ;
  debug_channel := Some (open_out_gen [Open_append ; Open_creat] 0o666 debug_file_name)

let get_ch () =
  match !debug_channel with
  | Some ch -> ch
  | None -> raise (Error.Violation "Tried to get a debug file channel while none was open")

let should_print (verbose:bool) : bool =
  let is_on_verbose = verbose || !in_verbose_sec in
  match !debug_on, !debug_verbose, is_on_verbose with
  | false, _ , _ -> false
  | true, false, true -> false
  | true, false, false -> true
  | true, true, _ -> true

let print ?(verbose=false) (f : unit -> string) : unit =
  if should_print verbose then
    let indent = Util.concat_n_times !debug_indent debug_indent_string in
    let new_line_indent = "\n" ^ indent ^ "↳ " in
    let re = Str.regexp "\n" in
    let s = Str.global_replace re new_line_indent (f()) in
    (output_string (get_ch()) (indent ^ s ^ "\n");
     flush (get_ch()))
  else ()




let print_string s = print (fun () -> s)

let print_and_ret (f : unit -> string) (value : 'a) (pf : 'a -> string) : 'a =
  print f ;
  print (fun () -> pf value) ;
  value

let indent () = debug_indent := !debug_indent + 1

let deindent () = if !debug_indent > 0 then debug_indent := !debug_indent - 1

let begin_verbose () = in_verbose_sec := true

let end_verbose () = in_verbose_sec := false

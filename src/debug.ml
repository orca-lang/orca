open Printf

let debug_on = ref false
let debug_channel : (out_channel option) ref = ref None
let debug_file_name = "debug.out"

let set_debug_on () =
  debug_on := true ;
  debug_channel := Some (open_out debug_file_name)

let get_ch () =
  match !debug_channel with
  | Some ch -> ch
  | None -> raise (Error.Violation "Tried to get a debug file channel while none was open")

let print (f : unit -> string) : unit =
  if !debug_on then
    (output_string (get_ch()) (f () ^ "\n");
     flush (get_ch()))
  else ()

let print_string s = print (fun () -> s)

let print_and_ret (f : unit -> string) (value : 'a) (pf : 'a -> string) : 'a =
  print f ;
  print (fun () -> pf value) ;
  value

open Parser

exception Error of string

let regexp nl  = ('\n' | '\r' | "\r\n" | "\n\r")
let regexp tab = ['\t''\x0b']
let regexp wsp = [' ''\t']
let regexp digit = ['0' - '9']+
let regexp numeral = digit+

let regexp lower = ['a'-'z']
let regexp upper = ['A'-'Z']

(* Old regexp: (lower | upper) (lower | upper | digit)* *)
let regexp identifier = [^ '\x09'-'\x0a' '\x20' '\x0d' '(' ')' ':' ',' '\\' '.']+

(* Managing source code positions *)

let initial_pos file_name = { Lexing.pos_fname = file_name
			    ; Lexing.pos_lnum = 1
			    ; Lexing.pos_bol = 0
			    ; Lexing.pos_cnum = 0
			    }
let add_line pos = { pos with
		     Lexing.pos_lnum = pos.Lexing.pos_lnum +1
		   ; Lexing.pos_bol = pos.Lexing.pos_bol + pos.Lexing.pos_cnum
		   ; Lexing.pos_cnum = 0
		   }
let add_word pos length = { pos with Lexing.pos_cnum = pos.Lexing.pos_cnum + length }

let remove_set s = String.sub s 3 (String.length s - 3)

let rec main_scanner pos = lexer
  | wsp | tab -> main_scanner (add_word pos 1) lexbuf (* ignore whitespace *)
  | nl -> main_scanner (add_line pos) lexbuf   (* ignores new lines *)
  | "(*)" -> linecomment (add_word pos (Ulexing.lexeme_length lexbuf)) lexbuf
  | "(*" -> comment pos 0 lexbuf
  | eof -> add_word pos (Ulexing.lexeme_length lexbuf), EOF

  | "data" -> add_word pos (Ulexing.lexeme_length lexbuf), DATA
  | "syn" -> add_word pos (Ulexing.lexeme_length lexbuf), SYN
  | "def" | "thm" | "lem" -> add_word pos (Ulexing.lexeme_length lexbuf), DEF
  | "|" -> add_word pos (Ulexing.lexeme_length lexbuf), MID
  | "=>" -> add_word pos (Ulexing.lexeme_length lexbuf), RARR
  | "->" -> add_word pos (Ulexing.lexeme_length lexbuf), ARR
  | "->>" -> add_word pos (Ulexing.lexeme_length lexbuf), SARR
  | ":" -> add_word pos (Ulexing.lexeme_length lexbuf), COLON
  | "," -> add_word pos (Ulexing.lexeme_length lexbuf), COMMA
  | ";" -> add_word pos (Ulexing.lexeme_length lexbuf), SEMICOLON
  | "^" numeral -> add_word pos (Ulexing.lexeme_length lexbuf), SHIFT (int_of_string (Ulexing.utf8_lexeme lexbuf))
  | "^" -> add_word pos (Ulexing.lexeme_length lexbuf), EMPTYS
  | ".." -> add_word pos (Ulexing.lexeme_length lexbuf), SHIFT 0
  | "0" ->  add_word pos (Ulexing.lexeme_length lexbuf), NIL
  | "[" -> add_word pos (Ulexing.lexeme_length lexbuf), LSQUARE
  | "]" -> add_word pos (Ulexing.lexeme_length lexbuf), RSQUARE
  | "fn" -> add_word pos (Ulexing.lexeme_length lexbuf), FN
  | '\\' -> add_word pos (Ulexing.lexeme_length lexbuf), LAM
  | "." -> add_word pos (Ulexing.lexeme_length lexbuf), DOT
  | "'" -> add_word pos (Ulexing.lexeme_length lexbuf), APPL
  | "*" -> add_word pos (Ulexing.lexeme_length lexbuf), STAR
  | "|-" -> add_word pos (Ulexing.lexeme_length lexbuf), TURNSTILE
  | ":>" -> add_word pos (Ulexing.lexeme_length lexbuf), TTS
  | "(" -> add_word pos (Ulexing.lexeme_length lexbuf), LPAREN
  | ")" -> add_word pos (Ulexing.lexeme_length lexbuf), RPAREN
  | "{" -> add_word pos (Ulexing.lexeme_length lexbuf), LCURLY
  | "}" -> add_word pos (Ulexing.lexeme_length lexbuf), RCURLY
  | "_" -> add_word pos (Ulexing.lexeme_length lexbuf), UNDERSCORE
  | "where" -> add_word pos (Ulexing.lexeme_length lexbuf), WHERE
  | "=" -> add_word pos (Ulexing.lexeme_length lexbuf), EQ
  | "set" numeral -> add_word pos (Ulexing.lexeme_length lexbuf), SET (int_of_string (remove_set (Ulexing.utf8_lexeme lexbuf)))
  | "set" -> add_word pos (Ulexing.lexeme_length lexbuf), SET 0
  | identifier -> add_word pos (Ulexing.lexeme_length lexbuf), IDENT (Ulexing.utf8_lexeme lexbuf)


and comment pos level = lexer
  | "(*)" -> comment (add_word pos 2) level lexbuf
  | "*)" -> if level = 0 then main_scanner (add_word pos 2) lexbuf else comment (add_word pos 2) (level-1) lexbuf
  | "(*" -> comment (add_word pos 2) (level+1) lexbuf
  | "\n" -> comment (add_line pos) level lexbuf
  | eof -> raise (Error "Found end of file inside of a block comment.\n\nPlease close comment block.")
  | _ -> comment (add_word pos (Ulexing.lexeme_length lexbuf)) level lexbuf

and linecomment pos = lexer
    | nl -> main_scanner (add_line pos) lexbuf
    | _  -> linecomment (add_word pos (Ulexing.lexeme_length lexbuf)) lexbuf
    | eof -> add_word pos (Ulexing.lexeme_length lexbuf), EOF

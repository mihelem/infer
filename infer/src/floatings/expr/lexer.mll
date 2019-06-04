{
  open Lexing
  open Parser

  exception Error of string
(*  exception SyntaxError of string *)

}

let eol = '\r' | '\n' | "\r\n"
let whitespace = [' ' '\t']
let id = ['a'-'z' 'A'-'Z' '_' '\'']['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']*
let ufloating = ['0'-'9']+['.']+['0'-'9']*

rule line = parse
  | ([^'\n']* '\n') as line { Some line, true }
  | eof { None, false }
  | ([^'\n']+ as line) eof {Some (line ^ "\n"), false }

and token = parse
  | whitespace+ { token lexbuf }
  | whitespace*eol { EOL }
  | id {IDENTIFIER (Lexing.lexeme lexbuf)}
  | ufloating as lxm {CFLOAT (lxm)}
  | '+' { PLUS }
  | '-' { MINUS }
  | '/' { DIV }
  | '*' { MULT }
  | '(' { LPAR }
  | ')' { RPAR }
  | "&&" { LAND }
  | "||" { LOR }
  | "!=" { NE }
  | "<=" { LE }
  | ">=" { GE }
  | "==" { EQ }
  | '<' { LT }
  | '>' { GT }
  | '!' { NOT }
  | _ { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }


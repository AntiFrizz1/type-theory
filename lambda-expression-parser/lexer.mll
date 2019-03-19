{
  open Parser       
  exception Eof
}


let digit = ['0' - '9']
let alpha = ['a' - 'z' 'A' - 'Z']
let value = alpha (alpha | digit | '\'')*
rule token = parse
   [' ' '\t' '\r' '\n']+     { token lexbuf }     
 | value                   { VALUE(Lexing.lexeme lexbuf) }
 | '.'                      { DOT }
 | '\\'                     { BSLASH }
 | '('                      { LPAREN }
 | ')'                      { RPAREN }
 | eof                      { EOF }
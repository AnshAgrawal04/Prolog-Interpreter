{
  exception InvalidToken of char ;;
  open Parser;;
}
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alphabet = lower | upper
let identifier = lower (alphabet | digit | '_')*  | ("\"" [^ '\"']+ "\"")
let variable = ['_' 'A'-'Z'] (alphabet | digit | '_')*
let comment = '/' '*' [^ '*' '/' ]* '*' '/'
let comment2 = "---" [^ '\n' ]* '\n'
let number = '0'| ['1'-'9'] ['0'-'9']* 

rule read = parse
    eof   {EOF}
  |  [' ' '\t' '\n']      {read lexbuf}
  | variable as v          {VAR(v)}
  | identifier as id     {CONS(id)} 
  | number as n           {NUM(int_of_string n)}
  | '('                   {LP}
  | ')'                   {RP}
  | '['                   {LB}
  | ']'                   {RB}
  | ','                   {COMMA}
  | '='                   {EQ}
  | "\\="                 {NOT_EQ}
  | '|'                   {PIPE}
  | '!'                   {CUT}
  | '.'                   {DOT}
  | ":-"                  {RULESYM}
  | '+'                   {PLUS}
  | '-'                   {MINUS}
  | '*'                   {TIMES}
  | '/'                   {DIV}
  | '%'                   {single_line_comment lexbuf}
  | comment2         {single_line_comment lexbuf}
  | '>'                   {GT}
  | '<'                   {LT}
  | _ as s                {raise (InvalidToken s)}

and single_line_comment = parse
    eof                   {EOF}
  | '\n'                  {read lexbuf}
  |   _                   {single_line_comment lexbuf}



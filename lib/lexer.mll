{
    open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let id = ['a'-'z']+

rule read =
    parse 
    | white { read lexbuf }

    | "/" { DIV }
    | "+" { PLUS }
    | "*" { TIMES }
    | "-" { MINUS }
    | "%"   { MOD }
    | "**"   { EXP }
    | "!" { NOT }
    | "&&" { AND }
    | "||" { OR }
    | "<" { LT }
    | ">" { GT }
    | "<=" { LEQ }
    | ">=" { GEQ }
    | "==" { EQ }
    | "!=" { NEQ }   

    | "=" { ASSIGN }
    | ";" { SEMICOLON }
    | "(" { LPAREN }
    | ")" { RPAREN }
    | "." { DOT }
    | "{" { LBRACE }
    | "}" { RBRACE }
    | "[" { LBRACKET }
    | "]" { RBRACKET }
    | "," { COMMA }

    | "contract" { CONTRACT }
    | "function" { FUNCTION }
    | "constructor" { CONSTRUCTOR }
    | "new" { NEW }
    | "value" { VALUE }
    | "sender" { SENDER }

    | "revert" { REVERT }
    | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | (id as s) { ID s }
    | "true" { TRUE }
    | "false" { FALSE }
    | "msg.sender" { MSGSENDER }
    | "address" { ADDRESS }
    | "msg.value" { MSGVALUE }
    | "transfer" { MSGVALUE }
    | "this" { THIS }
    | "if" { IF }
    | "else" { ELSE }
    | "return" { RETURN }

    | eof { EOF }
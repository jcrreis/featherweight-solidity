{
    let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }

    open Parser
}

let white = [' ' '\t']+
let eol = white*("\r")?"\n"
let digit = ['0'-'9']
let int = '-'? digit+
let id = ['a'-'z']+

rule read =
    parse 
    | white { read lexbuf }
    | eol
        { incr_linenum lexbuf;
          read lexbuf
        }

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
    | "mapping" { MAPPING }
    | "msg.sender" { MSGSENDER }
    | "address" { ADDRESS }
    | "msg.value" { MSGVALUE }
    | "transfer" { TRANSFER }
    | "this" { THIS }
    | "if" { IF }
    | "else" { ELSE }
    | "return" { RETURN }

    | eof { EOF }   
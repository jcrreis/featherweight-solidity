{
    let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }

open Parser

let keywords = Hashtbl.create 64

let () =
  List.iter (fun (k, v) -> Hashtbl.add keywords k v)
    [ ("contract", CONTRACT);
      ("function", FUNCTION);
      ("constructor", CONSTRUCTOR);
      ("new", NEW);
      ("value", VALUE);
      ("sender", SENDER);
      ("revert", REVERT);
      ("true", TRUE);
      ("false", FALSE);
      ("mapping", MAPPING);
      (* ("msgsender", MSGSENDER); *)
      ("address", ADDRESS);
      (* ("msgvalue", MSGVALUE); *)
      ("transfer", TRANSFER);
      ("this", THIS);
      ("if", IF);
      ("else", ELSE);
      ("return", RETURN);
      ("bool", BOOL); 
      ("uint", UINT);  
      ("msg", MSG);
    ]


let find_keyword k =
  try Hashtbl.find keywords k
  with Not_found -> ID k


}

let white = [' ' '\t']+
let eol = white*("\r")?"\n"
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let int = '-'? digit+
let id = (alpha) (alpha|digit|'_')*


rule read =
    parse
    | white { read lexbuf }
    | eol
        { incr_linenum lexbuf;
          read lexbuf
        }

    | "=" { ASSIGN }
    
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

    | ";" { SEMICOLON }
    | "(" { LPAREN }
    | ")" { RPAREN }
    | "." { DOT }
    | "{" { LBRACE }
    | "}" { RBRACE }
    | "[" { LBRACKET }
    | "]" { RBRACKET }
    | "," { COMMA }

    | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | (id as s) { find_keyword s }

    | eof { EOF }

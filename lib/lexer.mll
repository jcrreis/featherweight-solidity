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
      ("msg.sender", MSGSENDER);
      ("address", ADDRESS);
      ("msg.value", MSGVALUE);
      ("transfer", TRANSFER);
      ("this", THIS);
      ("if", IF);
      ("else", ELSE);
      ("return", RETURN);
      ("bool", BOOL); 
      ("uint", UINT);  
    ]

let match_str_with_regex s = 
  let idregex = Str.regexp "['a'-'z']+" in
  if Str.string_match idregex s 0 then ID s else CONTRACT_ID s 


let find_keyword k =
  try Hashtbl.find keywords k
  with Not_found -> match_str_with_regex k



}

let white = [' ' '\t']+
let eol = white*("\r")?"\n"
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let int = '-'? digit+
let id = (alpha) (alpha|digit|'_')*
let contract_id = alpha+

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

    | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | (id as s) { find_keyword s }
    | (contract_id as s) { find_keyword s }

    | eof { EOF }


// VALUES
%token <int> INT
%token <string> ID
%token TRUE
%token FALSE
%token MAPPING

%token CONTRACT
%token FUNCTION
%token CONSTRUCTOR
%token NEW
%token VALUE
%token SENDER

%token BOOL
%token UINT


// ARITHMETIC OPERATORS
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token EXP


// BOOLEAN OPERATORS
%token EQ
%token NEQ
%token LT
%token GT
%token LEQ
%token GEQ
%token AND
%token OR
%token NOT

// OPERATORS
// %token ARITOP
// %token BOOLOP
%token MSGSENDER
%token MSGVALUE
%token BALANCE
%token ADDRESS
%token THIS
%token IF
%token ELSE
// %token STATEREAD
// %token STATEWRITE
%token TRANSFER
%token REVERT
%token RETURN

// %token CONS
// %token SEQ

// PUNCTUATION
%token LPAREN
%token RPAREN
%token ASSIGN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
// %token LEFT_BRACK
// %token RIGHT_BRACK
%token DOT
// %token COLON
%token COMMA
%token EOF
%token SEMICOLON

// %nonassoc RETURN

%nonassoc SEMICOLON LBRACKET ELSE ASSIGN
%left EQ NEQ LT GT LEQ GEQ AND OR NOT
%left PLUS MINUS MOD  
%left TIMES DIV EXP 
%nonassoc DOT 

%start <Fs.expr> prog

%%


prog :
    | e = expr; EOF { e }
    | e = contract ; EOF { e }
    ;

contract:
  | CONTRACT contract_name = ID LBRACE state_variables = list(state_var_def);
      CONSTRUCTOR LPAREN; le1 = separated_list(COMMA, declare_variable); RPAREN LBRACE; e1 = fun_body ;RBRACE
      le2 = list(fun_def) RBRACE {
                          Fs.AddContract({
                                  name = contract_name;
                                  state = state_variables;
                                  constructor = (le1, e1);
                                  functions = le2;
                          })
                          }
  | c1 = contract; c2 = contract; { Seq (c1, c2) }
  ;

return_expr:
  | RETURN e = expr SEMICOLON { Fs.Return (e) }
  ;

statement:
  | e = expr SEMICOLON { e }
  ;
expr:
    | i = INT { Val(VUInt i) }
    | s = ID { Var s }
    | TRUE { Val(VBool True) }
    | FALSE { Val(VBool False) }
    | MAPPING t_e = typ { Val(VMapping(Hashtbl.create 64, t_e)) }                                       //mapping(type1 => type2)
    | e1 = expr; PLUS; e2 = expr { AritOp(Plus(e1, e2)) }
    | e1 = expr; DIV; e2 = expr { AritOp(Div(e1, e2)) }
    | e1 = expr; TIMES; e2 = expr { AritOp(Times(e1, e2)) }
    | e1 = expr; MINUS; e2 = expr { AritOp(Minus(e1, e2)) }
    | e1 = expr; MOD; e2 = expr { AritOp(Mod(e1, e2)) }
    | e1 = expr; EXP; e2 = expr { AritOp(Exp(e1, e2)) }
    | NOT; e = expr { BoolOp(Neg(e))}
    | e1 = expr; EQ; e2 = expr { BoolOp(Equals(e1, e2)) }
    | e1 = expr; NEQ; e2 = expr { BoolOp(Inequals(e1, e2)) }
    | e1 = expr; LT; e2 = expr { BoolOp(Lesser(e1, e2)) }
    | e1 = expr; GT; e2 = expr { BoolOp(Greater(e1, e2)) }
    | e1 = expr; LEQ; e2 = expr { BoolOp(LesserOrEquals(e1, e2)) }
    | e1 = expr; GEQ; e2 = expr { BoolOp(GreaterOrEquals(e1, e2)) }
    | e1 = expr; AND; e2 = expr { BoolOp(Conj(e1, e2)) }
    | e1 = expr; OR; e2 = expr { BoolOp(Disj(e1, e2)) }
    | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Call (e1, fname, e2, le) }
    | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN DOT SENDER LPAREN; e3 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { CallTopLevel (e1, fname, e2, e3, le) }
    | MSGSENDER { MsgSender }
    | MSGVALUE { MsgValue }
    | e1 = expr; DOT TRANSFER LPAREN; e2 = expr ;RPAREN{ Transfer (e1, e2) }
    | ADDRESS LPAREN; e = expr ;RPAREN{ Address (e) }
    | THIS DOT s = option(ID) { This s }
    | e = expr; DOT BALANCE { Balance (e) }
    | e = expr; DOT s = ID { StateRead (e, s) }
    | s = ID LPAREN; e = expr; RPAREN { Cons (s, e) }
    | e1 = expr; SEMICOLON; e2 = expr; SEMICOLON { Seq (e1, e2) }
    // this.balance = 0 || balance = 0  e | id
    | THIS DOT s = ID ; ASSIGN; e1 = expr { StateAssign (This None, s, e1) }
    // | e1 = expr; DOT s = ID ; ASSIGN ; e2 = expr { StateAssign (e1, s, e2) }
    | s = ID ; ASSIGN ; e = expr { Assign (s, e) }
  
    | e1 = expr; LBRACKET; e2 = expr; RBRACKET { MapRead (e1, e2) }
    | e1 = expr; LBRACKET; e2 = expr; RBRACKET ASSIGN ; e3 = expr { MapWrite (e1, e2, e3) }
    // | NEW; _contract_name = ID; _e = expr { Revert }
    | NEW; contract_name = ID; DOT VALUE LPAREN; e = expr; RPAREN LPAREN;  le = separated_list(COMMA,expr); RPAREN { New (contract_name, e, le) }
    | REVERT { Revert }
    | IF LPAREN; e1 = expr; RPAREN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
    | v = declare_variable; ASSIGN; e1 = expr; SEMICOLON; e2 = expr; { 
      let (t_e, s) = v in 
      Let(t_e, s, e1, e2) 
    }
  ;


declare_variable:
     | t_e = typ s = ID { (t_e, s) }
     ;

state_var_def:
    | e = declare_variable SEMICOLON { e }

fun_def:
    | FUNCTION fname = ID LPAREN; le = separated_list(COMMA, declare_variable);
      RPAREN LBRACE; e = fun_body; RBRACE {
        Fs.{ name = fname;
            rettype = Unit;
            args = le;
            body = e;
    } }

// state_variables:
//   sv = option(separated_list(SEMICOLON, declare_variable) SEMICOLON) {
//     match sv with 
//       | None -> []
//       | Some sv -> sv
//   }

fun_body: 
  | e1 = option(statement) ; e2 = option(return_expr) { 
    match e1, e2 with
      | None, None -> Seq(Val(VUnit), Val(VUnit))
      | None, Some e2 -> Seq(Val(VUnit), e2) 
      | Some e1, None -> Seq(e1, Val(VUnit))  
      | Some e1, Some e2 -> Seq(e1, e2)   
  }

typ:
     | UINT { Fs.UInt }
     | ADDRESS { Fs.Address }
     | BOOL { Fs.Bool }
     | MAPPING LPAREN key = typ; ASSIGN GT value = typ RPAREN
       { Fs.Map (key, value) }

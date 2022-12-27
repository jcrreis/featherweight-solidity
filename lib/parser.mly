
// VALUES
%token <int> INT
%token <string> ID
%token TRUE
%token FALSE

%token CONTRACT
%token FUNCTION
%token CONSTRUCTOR
%token NEW
%token VALUE
%token SENDER

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

// %token NEW 
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


%start <Fs.expr> prog

%%

prog :
    | e = expr; EOF { e }
    ;

expr:
    | i = INT { Val(VUInt i) }
    | s = ID { Var s }
    | TRUE { Val(VBool True) }
    | FALSE { Val(VBool False) }
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
    | MSGSENDER { MsgSender }
    | MSGVALUE { MsgValue }
    | ADDRESS LPAREN; e = expr ;RPAREN{ Address (e) }
    | THIS DOT s = option(ID) { This s }
    | e1 = expr; DOT TRANSFER LPAREN; e2 = expr ;RPAREN{ Transfer (e1, e2) }
    | e = expr; DOT BALANCE { Balance (e) }
    | e = expr; DOT s = ID { StateRead (e, s) }
    | s = ID LPAREN; e = expr; RPAREN { Cons (s, e) }
    | e1 = expr; SEMICOLON; e2 = expr { Seq (e1, e2) }
    | s = ID ; ASSIGN ; e = expr { Assign (s, e) }
    | e1 = expr; DOT s = ID ; ASSIGN ; e2 = expr { StateAssign (e1, s, e2) }
    | e1 = expr; LBRACKET; e2 = expr; RBRACKET { MapRead (e1, e2) } 
    | e1 = expr; LBRACKET; e2 = expr; RBRACKET ASSIGN ; e3 = expr { MapWrite (e1, e2, e3) }
    | NEW contract_name = ID LPAREN; e = expr; RPAREN LPAREN; le = list(expr); RPAREN { New (contract_name, e, le) }
    | REVERT { Revert }
    | IF LPAREN; e1 = expr; RPAREN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
    | RETURN e = expr { Return (e) } 
    | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Call (e1, fname, e2, le) }
    | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN DOT SENDER LPAREN; e3 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { CallTopLevel (e1, fname, e2, e3, le) }

    // | CONTRACT contract_name = ID LBRACE RBRACE CONSTRUCTOR LPAREN RPAREN LBRACE RBRACE list(declare_function) RBRACE { Revert }
    // | FUNCTION LPAREN; ;RPAREN LBRACE; e = expr; RBRACE { Revert }
    ;


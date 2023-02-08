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
%token MSGSENDER
%token MSGVALUE
%token BALANCE
%token ADDRESS
%token THIS
%token IF
%token ELSE
%token TRANSFER
%token REVERT
%token RETURN

// PUNCTUATION
%token LPAREN
%token RPAREN
%token ASSIGN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token DOT
// %token COLON
%token COMMA
%token EOF
%token SEMICOLON


%nonassoc SEMICOLON LBRACKET ASSIGN
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

arit_expr: 
  | e1 = expr; PLUS; e2 = expr { AritOp(Plus(e1, e2)) }
  | e1 = expr; DIV; e2 = expr { AritOp(Div(e1, e2)) }
  | e1 = expr; TIMES; e2 = expr { AritOp(Times(e1, e2)) }
  | e1 = expr; MINUS; e2 = expr { AritOp(Minus(e1, e2)) }
  | e1 = expr; MOD; e2 = expr { AritOp(Mod(e1, e2)) }
  | e1 = expr; EXP; e2 = expr { AritOp(Exp(e1, e2)) }
  ;
bool_expr:
  | NOT; e = expr { BoolOp(Neg(e))}
  | e1 = expr; EQ; e2 = expr { BoolOp(Equals(e1, e2)) }
  | e1 = expr; NEQ; e2 = expr { BoolOp(Inequals(e1, e2)) }
  | e1 = expr; LT; e2 = expr { BoolOp(Lesser(e1, e2)) }
  | e1 = expr; GT; e2 = expr { BoolOp(Greater(e1, e2)) }
  | e1 = expr; LEQ; e2 = expr { BoolOp(LesserOrEquals(e1, e2)) }
  | e1 = expr; GEQ; e2 = expr { BoolOp(GreaterOrEquals(e1, e2)) }
  | e1 = expr; AND; e2 = expr { BoolOp(Conj(e1, e2)) }
  | e1 = expr; OR; e2 = expr { BoolOp(Disj(e1, e2)) }
  ;
values: 
  | i = INT { Val(VUInt i) }
  | s = ID { Var s }
  | TRUE { Val(VBool True) }
  | FALSE { Val(VBool False) }
  | MAPPING t_e = typ { Fs.Val(VMapping(Hashtbl.create 64, t_e)) }      
  | MSGSENDER { Fs.MsgSender }
  | MSGVALUE { Fs.MsgValue }                          
  ;

if_statement:
  | IF LPAREN; e1 = expr; RPAREN; LBRACE; e2 = option(statement); RBRACE ;ELSE; LBRACE; e3 = option(statement); RBRACE { 
    match e2, e3 with 
      | None, None -> Fs.If(e1, Val(VUnit), Val(VUnit))
      | None, Some e3 -> Fs.If(e1, Val(VUnit), e3) 
      | Some e2, None -> Fs.If(e1, e2, Val(VUnit))  
      | Some e2, Some e3 -> Fs.If(e1, e2, e3)          
    }
  ;

deploy_new_contract:
  | NEW; contract_name = ID; DOT VALUE LPAREN; e = expr; RPAREN LPAREN;  le = separated_list(COMMA,expr); RPAREN { New (contract_name, e, le) }
  ;

function_calls: 
  | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Fs.Call (e1, fname, e2, le) }
  | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN DOT SENDER LPAREN; e3 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Fs.CallTopLevel (e1, fname, e2, e3, le) }
  ;

solidity_special_functions:
  | e1 = expr; DOT TRANSFER LPAREN; e2 = expr ;RPAREN{ Fs. Transfer (e1, e2) }
  | ADDRESS LPAREN; e = expr ;RPAREN{ Fs.Address (e) }
  | e = expr; DOT BALANCE { Fs.Balance (e) }
  ;

this_statements:
  | THIS DOT s = option(ID) { This s }
  | THIS DOT s = ID ; ASSIGN; e1 = expr { Fs.StateAssign (This None, s, e1) }
  ;

variables:
  | v = declare_variable; ASSIGN; e1 = expr; SEMICOLON; e2 = expr; { 
    let (t_e, s) = v in 
    Let(t_e, s, e1, e2) 
  }
  | e = expr; DOT s = ID { StateRead (e, s) }
  | e1 = expr; DOT s = ID ; ASSIGN ; e2 = expr { Fs.StateAssign (e1, s, e2) }
  ;

map_read_write:
  | e1 = expr; LBRACKET; e2 = expr; RBRACKET { MapRead (e1, e2) }
  | e1 = expr; LBRACKET; e2 = expr; RBRACKET ASSIGN ; e3 = expr { Fs.MapWrite (e1, e2, e3) }
  ;

expr:
  | v = values { v }
  | a = arit_expr { a }   
  | b = bool_expr { b }
  | f = function_calls { f }
  | ssf = solidity_special_functions { ssf }
  | t = this_statements { t }
  | m = map_read_write { m }
  | vars = variables { vars }
  | s = ID LPAREN; e = expr; RPAREN { Cons (s, e) }
  | e1 = expr; SEMICOLON; e2 = expr { Seq (e1, e2) }
  | s = ID ; ASSIGN ; e = expr { Assign (s, e) }
  | REVERT { Revert }
  | e = deploy_new_contract { e }
  | e = if_statement { e }
  
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

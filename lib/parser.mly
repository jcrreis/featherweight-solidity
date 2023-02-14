//VALUES
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
%left PLUS MINUS MOD  
%left TIMES DIV EXP 
%left EQ NEQ LT GT LEQ GEQ AND OR NOT
%nonassoc DOT

%start <Types.expr> prog

%%


prog :
  | e = expr; EOF { e }
  | e = contract ; EOF { e }
  ;

contract:
  | CONTRACT contract_name = ID LBRACE state_variables = list(state_var_def);
      CONSTRUCTOR LPAREN; le1 = separated_list(COMMA, declare_variable); RPAREN LBRACE; e1 = fun_body ;RBRACE
      le2 = list(fun_def) RBRACE {
                          Types.AddContract({
                                  name = contract_name;
                                  state = state_variables;
                                  constructor = (le1, e1);
                                  functions = le2;
                          })
                          }
  | c1 = contract; c2 = contract; { Seq (c1, c2) }
  ;

return_expr:
  | RETURN e = expr SEMICOLON { Types.Return (e) }
  ;


statement:
  | e = expr SEMICOLON { e }
  | e = if_statement { e }
  | e1 = statement; e2 = statement { Types.Seq(e1, e2) }
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
  | i = INT { Format.eprintf "PASSEI NO VUInt @.";Val(VUInt i) }
  | s = ID { Format.eprintf "PASSEI NO  %s  @." s; Var s }
  | TRUE { Format.eprintf "PASSEI NO True @.";Val(VBool True) }
  | FALSE { Format.eprintf "PASSEI NO False @.";Val(VBool False) }
  | MAPPING t_e = typ { Format.eprintf "PASSEI NO VMapping @.";Types.Val(VMapping(Hashtbl.create 64, t_e)) }      
  | MSGSENDER { Format.eprintf "PASSEI NO MsgSender @.";Types.MsgSender }
  | MSGVALUE { Format.eprintf "PASSEI NO MsgValue @.";Types.MsgValue }                          
  ;

if_statement:
  | IF LPAREN; e1 = expr; RPAREN; LBRACE; e2 = option(statement); RBRACE ;ELSE; LBRACE; e3 = option(statement); RBRACE { 
    match e2, e3 with 
      | None, None -> Types.If(e1, Val(VUnit), Val(VUnit))
      | None, Some e3 -> Types.If(e1, Val(VUnit), e3) 
      | Some e2, None -> Types.If(e1, e2, Val(VUnit))  
      | Some e2, Some e3 -> Types.If(e1, e2, e3)          
    }
  | IF LPAREN; e1 = expr; RPAREN; LBRACE; e2 = option(statement); RBRACE {
    match e2 with
      | None -> Types.If(e1, Val(VUnit), Val(VUnit))
      | Some e2 ->  Types.If(e1, e2, Val(VUnit))
  }
  ;

deploy_new_contract:
  | NEW; contract_name = ID; DOT VALUE LPAREN; e = expr; RPAREN LPAREN;  le = separated_list(COMMA,expr); RPAREN { New (contract_name, e, le) }
  ;

function_calls: 
  | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Types.Call (e1, fname, e2, le) }
  | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN DOT SENDER LPAREN; e3 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Types.CallTopLevel (e1, fname, e2, e3, le) }
  ;

solidity_special_functions:
  | e1 = expr; DOT TRANSFER LPAREN; e2 = expr ;RPAREN{ Types. Transfer (e1, e2) }
  | ADDRESS LPAREN; e = expr ;RPAREN{ Types.Address (e) }
  | e = expr; DOT BALANCE { Types.Balance (e) }
  ;

this_statements:
  | THIS { Types.This None }
  // | THIS DOT s = ID { Format.eprintf "PASSEI NO this.%s @." s; Types.This (Some s) }
  ;

variables:
  | v = declare_variable; ASSIGN; e1 = expr; SEMICOLON; e2 = expr; { 
    let (t_e, s) = v in 
    Let(t_e, s, e1, e2) 
  }
  | e = expr; DOT s = ID { Format.eprintf "PASSEI NO STATEREAD @.";StateRead (e, s) }
  | e1 = expr; DOT s = ID ; ASSIGN ; e2 = expr { Format.eprintf "PASSEI NO STATEASSIGN @.";Types.StateAssign (e1, s, e2) }
  ;

map_read_write:
  | e1 = expr; LBRACKET; e2 = expr; RBRACKET { Format.eprintf "PASSEI NO MAPREAD @.";MapRead (e1, e2) }
  | e1 = expr; LBRACKET; e2 = expr; RBRACKET ASSIGN ; e3 = expr { Types.MapWrite (e1, e2, e3) }
  ;


expr:
  | vars = variables { Format.eprintf "PASSEI NO vars @.";vars }
  | v = values { Format.eprintf "PASSEI NO expr values @.";  v }
  | a = arit_expr { Format.eprintf "PASSEI NO a @.";a }   
  | b = bool_expr { Format.eprintf "PASSEI NO b @.";b }
  // | f = function_calls { Format.eprintf "PASSEI NO f @.";f }
  // | ssf = solidity_special_functions { Format.eprintf "PASSEI NO ssf @.";ssf }
  | t = this_statements { Format.eprintf "PASSEI NO t @.";t }
  | m = map_read_write { Format.eprintf "PASSEI NO m @.";m }
  // | s = ID LPAREN; e = expr; RPAREN { Format.eprintf "PASSEI NO Cons @.";Cons (s, e) }
  // | s = ID ; ASSIGN ; e = expr { Format.eprintf "PASSEI NO ASSIGN @.";Assign (s, e) }
  // | REVERT { Format.eprintf "PASSEI NO revert @.";Revert }
  // // // x = 1 
  // | e = deploy_new_contract { Format.eprintf "PASSEI NO deploy_new_contract @.";e }
  // | e = if_statement { Format.eprintf "PASSEI NO if_statement @.";e }
  
  ;


declare_variable:
  | t_e = typ s = ID { (t_e, s) }
  ;

state_var_def:
  | e = declare_variable SEMICOLON { e }
  ;

fun_def:
  | FUNCTION fname = ID LPAREN; le = separated_list(COMMA, declare_variable);
    RPAREN LBRACE; e = fun_body; RBRACE {
      Types.{ name = fname;
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
  | UINT { Types.UInt }
  | ADDRESS { Types.Address }
  | BOOL { Types.Bool }
  | MAPPING LPAREN key = typ; ASSIGN GT value = typ RPAREN
    { Types.Map (key, value) }

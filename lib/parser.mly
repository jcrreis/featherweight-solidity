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
%token MSG
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
%token COLON
%token COMMA
%token EOF
%token SEMICOLON

//SYNTAX
%token RETURNS

%nonassoc SEMICOLON  
%right ASSIGN
%left PLUS MINUS MOD  
%left TIMES DIV EXP 
%left EQ NEQ LT GT LEQ GEQ AND OR NOT
%nonassoc LBRACKET
%left DOT

%start <Types.expr> prog

%%


prog :
  | e = expr; EOF { e }
  | e = contract ; EOF { e }
  ;

typ:
  | UINT { Types.UInt }
  | ADDRESS { Types.Address (None)}
  | BOOL { Types.Bool }
  | MAPPING LPAREN key = typ; ASSIGN GT value = typ RPAREN
    { Types.Map (key, value) }
  ;

values: 
  | i = INT { Val(VUInt i) }
  | s = ID { Var s }
  | TRUE {  Val(VBool True) }
  | FALSE { Val(VBool False) }
  | MAPPING t_e = typ { Types.Val(VMapping(Hashtbl.create 64, t_e)) }      
  | MSGSENDER { Types.MsgSender }
  | MSGVALUE { Types.MsgValue }   
  // | MSG DOT "value" { Types.MsgSender }                       
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

map_read_write:
  | e1 = expr; LBRACKET; e2 = expr; RBRACKET { MapRead (e1, e2) }
  | e1 = expr; LBRACKET; e2 = expr; RBRACKET ASSIGN ; e3 = expr { Types.MapWrite (e1, e2, e3) }
  ;

this_statements:
  | THIS { Types.This None }
  ;

declare_variable:
  | t_e = typ s = ID {(t_e, s) }
  ;

state_vars:
  //state read/write
   | v = declare_variable; ASSIGN; e1 = expr; SEMICOLON; e2 = expr; { 
    Format.eprintf "AQUIII";
    let (t_e, s) = v in 
    Let(t_e, s, e1, e2) 
  }
  //special case shortener for maps
  
  | e = expr; DOT s = ID { StateRead (e, s) }
  | e1 = expr; DOT s = ID ; ASSIGN ; e2 = expr { Format.eprintf "AQUIIIIssasasd";Types.StateAssign (e1, s, e2) }
  // | e = expr; DOT s = ID LBRACKET e1 = expr RBRACKET ASSIGN e2 = expr {
  //   Types.StateAssign(e, s , MapWrite(StateRead(e, s), e1, e2))
  // }
  ;


expr:
  | s_vars = state_vars { s_vars }
  | v = values { v }
  | a = arit_expr { a }   
  | b = bool_expr { b }
  | f = function_calls { f }
  | ssf = solidity_special_functions { ssf }
  | t = this_statements { t }
  | m = map_read_write { m }
  | s = ID LPAREN; e = expr; RPAREN { Cons (s, e) }
  | s = ID ; ASSIGN ; e = expr { Assign (s, e) }
  | REVERT { Revert }
  // | e = deploy_new_contract { Format.eprintf "PASSEI NO deploy_new_contract @.";e }
  | e = if_statement { e }
  | LPAREN e = expr RPAREN { e }
  ;


return_expr:
  | RETURN e = expr SEMICOLON { Types.Return (e) }
  ;


statement:
  | e = expr SEMICOLON { e }
  | e = if_statement { e }
  | RETURN e = expr SEMICOLON { e }
  | e1 = statement; e2 = statement { Types.Seq(e1, e2) }
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

if_with_return:
   | IF LPAREN; e1 = expr; RPAREN; LBRACE; e2 = option(statement); e3 = return_expr RBRACE ;ELSE; LBRACE; e4 = option(statement); e5 = return_expr ;RBRACE { 
    match e2, e4 with 
      | None, None -> Types.If(e1, Seq(Val(VUnit), e3), Seq(Val(VUnit), e5))
      | None, Some e4 -> Types.If(e1, Seq(Val(VUnit), e3), Seq(e4, e5)) 
      | Some e2, None -> Types.If(e1, Seq(e2, e3), Seq(Val(VUnit), e5))  
      | Some e2, Some e4 -> Types.If(e1, Seq(e2, e3), Seq(e4, e5))          
    }
  | IF LPAREN; e1 = expr; RPAREN; LBRACE; e2 = option(statement); e3 = return_expr RBRACE {
    match e2 with
      | None -> Types.If(e1, Seq(Val(VUnit), e3), Val(VUnit))
      | Some e2 ->  Types.If(e1, Seq(e2, e3), Val(VUnit))
  }

fun_msg_value:
  | LBRACE VALUE COLON e = expr RBRACE { e }

function_calls: 
  | e1 = expr ; DOT fname = ID e2 = option(fun_msg_value) LPAREN; le = separated_list(COMMA,expr); RPAREN { 
    begin
      let e2 = match e2 with 
        | None -> Types.Val (VUInt 0)
        | Some e2 -> e2 
      in
      Types.Call (e1, fname, e2, le) 
    end
  }
  | e1 = expr ; DOT fname = ID DOT VALUE LPAREN; e2 = expr; RPAREN DOT SENDER LPAREN; e3 = expr; RPAREN LPAREN; le = separated_list(COMMA,expr); RPAREN { Types.CallTopLevel (e1, fname, e2, e3, le) }
  
  | expr ; DOT ; fname = ID  LPAREN; le = separated_list(COMMA,expr); RPAREN { Types.This (Some(fname, le)) }
  ;

solidity_special_functions:
  | e1 = expr; DOT TRANSFER LPAREN; e2 = expr ;RPAREN{ Types. Transfer (e1, e2) }
  | ADDRESS LPAREN; e = expr ;RPAREN{ Types.Address (e) }
  |   e = expr; DOT BALANCE  { Types.Balance (e) }
  ;



fun_type_return_declaration: 
  | RETURNS LPAREN t = typ RPAREN { t }
  ;

fun_def:
  | FUNCTION fname = ID LPAREN; le = separated_list(COMMA, declare_variable);
    RPAREN t = option(fun_type_return_declaration) LBRACE; e = fun_body; RBRACE {
      begin 
        let return_type = match t with 
          | None -> Types.Unit 
          | Some t -> t
        in 
        Types.{ name = fname;
                annotation = None;
                rettype = return_type;
                args = le;
                body = e;
        }
      end 
  }
  ;



fun_body:  
  | e1 = option(statement) ; e2 = option(return_expr) { 
    match e1, e2 with
      | None, None -> Seq(Val(VUnit), Val(VUnit))
      | None, Some e2 -> Seq(Val(VUnit), e2) 
      | Some e1, None -> Seq(e1, Val(VUnit))  
      | Some e1, Some e2 -> Seq(e1, e2)   
  }
 
  | e = if_with_return { e }
  ;

// CONTRACTS

deploy_new_contract:
  | NEW; contract_name = ID; DOT VALUE LPAREN; e = expr; RPAREN LPAREN;  le = separated_list(COMMA,expr); RPAREN { New (contract_name, e, le) }
  ;


state_var_def:
  | e = declare_variable SEMICOLON { e }
  ;

contract:
  | CONTRACT contract_name = ID LBRACE state_variables = list(state_var_def);
      CONSTRUCTOR LPAREN; le1 = separated_list(COMMA, declare_variable); RPAREN LBRACE; e1 = fun_body ;RBRACE
      le2 = list(fun_def) RBRACE {
                          Types.AddContract({
                                  name = contract_name;
                                  super_contracts = Class(contract_name, []);
                                  super_constructors_args = [];
                                  state = state_variables;
                                  constructor = (le1, e1);
                                  functions = le2;
                                  function_lookup_table = Hashtbl.create 64;
                          })
                          }
  | c1 = contract; c2 = contract; { Seq (c1, c2) }
  ;

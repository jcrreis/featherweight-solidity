module StateVars = Map.Make(String)

type t_exp =
  | C of int (* * hash_contract_code? *)
  | Bool
  | Unit
  | UInt
  | Address
  | Map of t_exp * t_exp
  | Fun of t_exp list * t_exp
  | TRevert

type b_val =
  | True
  | False


type values =
  | VBool of b_val
  | VUInt of int
  | VAddress of string
  | VUnit
  | VContract of int
  | VMapping of ((expr, expr) Hashtbl.t ) * t_exp


and arit_ops =
  | Plus of expr * expr
  | Div of expr * expr
  | Times of expr * expr
  | Minus of expr * expr
  | Exp of expr * expr
  | Mod of expr * expr

and bool_ops =
  | Neg of expr
  | Conj of expr * expr
  | Disj of expr * expr
  | Equals of expr * expr
  | Greater of expr * expr
  | GreaterOrEquals of expr * expr
  | Lesser of expr * expr
  | LesserOrEquals of expr * expr
  | Inequals of expr * expr

and expr =
  | AritOp of arit_ops
  | BoolOp of bool_ops
  | Var of string
  | Val of values
  | This of string option (*This ("") === This, else This.fname*)
  | MsgSender
  | MsgValue
  | Balance of expr
  | Address of expr
  | StateRead of expr * string
  | Transfer of expr * expr
  | New of string * expr * expr list
  | Cons of string * expr
  | Seq of expr * expr
  | Let of t_exp *  string * expr * expr 
  | Assign of string * expr
  | StateAssign of expr * string * expr
  | MapRead of expr * expr
  | MapWrite of expr * expr * expr
  | Call of expr * string * expr * expr list (* e.f.value(e)(le) *)
  | CallTopLevel of expr * string * expr * expr * expr list (* e.f.value(e).sender(e)(le) *)
  | Revert
  | If of expr * expr * expr
  | Return of expr
  | AddContract of contract_def

and fun_def = {
  name : string;
  rettype : t_exp;
  args : (t_exp * string) list;
  body : expr;
}

and contract_def = {
  name : string;
  state : (t_exp * string) list;
  constructor : (t_exp * string) list * expr;
  functions : fun_def list;
}



type contract_table = (string, contract_def) Hashtbl.t

type blockchain = ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t

type conf = (blockchain * blockchain * values Stack.t * expr)

type program = (contract_table * blockchain * expr)
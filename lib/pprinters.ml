open Types

let rec t_exp_to_string (t_e: t_exp) : string = match t_e with
| C (n) -> "contract" ^ "(" ^ (Stdlib.string_of_int n) ^ ")"
| Bool -> "boolean"
| Unit -> "unit"
| UInt -> "uint"
| Address -> "address"
| Map (t_e1, t_e2)-> "mapping(" ^ t_exp_to_string t_e1 ^ " => " ^ t_exp_to_string t_e2 ^ ")"
| TRevert -> "revert"
| Fun (lt_e, t_e) -> "Fun (" ^ (List.fold_left (fun s t_e -> s ^ t_exp_to_string t_e) "" lt_e) ^ ")" ^ " -> " ^ t_exp_to_string t_e


let rec print_tuples lst =
  begin match lst with
    | [] -> ()
    | (t_e, s) :: rest ->
      let s1 = t_exp_to_string t_e in
      Printf.printf "%s : %s;\n" s1 s;
      print_tuples rest
  end

let rec values_to_string (v: values) : string =
  match v with 
    | VUInt (e1) -> string_of_int e1
    | VBool (e1) -> begin match e1 with 
      | True -> "true"
      | False -> "false"
    end
    | VAddress (e1) -> e1
    | VContract (e1) -> "Contract " ^ (string_of_int e1)
    | VMapping (e1, _t_e) -> Hashtbl.fold (fun k v _s -> match k, v with
      | Val(v1), Val(v2) -> values_to_string v1 ^ " -> " ^ values_to_string v2
      | _ -> assert false) e1 ""
    | VUnit -> "Unit"
  
let rec expr_to_string (e: expr) : string =
  match e with 
    | AritOp (a1) -> begin match a1 with 
      | Plus (e1, e2) -> "(" ^ expr_to_string e1 ^ "+" ^ expr_to_string e2 ^ ")"
      | Minus (e1, e2) -> "(" ^ expr_to_string e1 ^ "-" ^ expr_to_string e2 ^ ")"
      | Times (e1, e2) -> "(" ^ expr_to_string e1 ^ "*" ^ expr_to_string e2 ^ ")"
      | Div (e1, e2) -> "(" ^ expr_to_string e1 ^ "/" ^ expr_to_string e2 ^ ")"
      | Mod (e1, e2) -> "(" ^ expr_to_string e1 ^ "%" ^ expr_to_string e2 ^ ")"
      | Exp (e1, e2) -> "(" ^ expr_to_string e1 ^ "**" ^ expr_to_string e2 ^ ")"
    end 
    | BoolOp (b1) -> begin match b1 with 
      | Conj (e1, e2) -> "(" ^ expr_to_string e1 ^ "&&" ^ expr_to_string e2 ^ ")"
      | Disj (e1, e2) -> "(" ^ expr_to_string e1 ^ "||" ^ expr_to_string e2 ^ ")"
      | Neg (e1) -> "~(" ^ expr_to_string e1 ^ ")"
      | Equals (e1, e2) -> "(" ^ expr_to_string e1 ^ "==" ^ expr_to_string e2 ^ ")"
      | Lesser (e1, e2) -> "(" ^ expr_to_string e1 ^ "<" ^ expr_to_string e2 ^ ")"
      | LesserOrEquals (e1, e2) -> "(" ^ expr_to_string e1 ^ "<=" ^ expr_to_string e2 ^ ")"
      | Greater (e1, e2) -> "(" ^ expr_to_string e1 ^ ">" ^ expr_to_string e2 ^ ")"
      | GreaterOrEquals (e1, e2) -> "(" ^ expr_to_string e1 ^ ">=" ^ expr_to_string e2 ^ ")"
      | Inequals (e1, e2) -> "(" ^ expr_to_string e1 ^ "!=" ^ expr_to_string e2 ^ ")"
    end
    | Var (s1) -> s1 
    | Val (v1) -> values_to_string v1
    | This (s1) -> begin match s1 with 
      | None -> "this"
      | Some s -> "this." ^ s
    end
    | MsgSender -> "msg.sender"
    | MsgValue -> "msg.value"
    | Balance (e1) -> "Balance(" ^ expr_to_string e1 ^ ")"
    | Address (e1) -> "Address(" ^ expr_to_string e1 ^ ")"
    | StateRead (e1, s1) -> expr_to_string e1 ^ "." ^ s1
    | Transfer (e1, e2) -> expr_to_string e1 ^ ".transfer(" ^ expr_to_string e2 ^ ")"
    | New (s1, e1, _el1) -> "new " ^ s1 ^ "(" ^ expr_to_string e1 ^ ")" 
    | Cons (s1, e1) -> s1 ^ "(" ^ expr_to_string e1 ^ ")"
    | Seq (e1, e2) -> "\n" ^ expr_to_string e1 ^ ";\n" ^ expr_to_string e2 ^ ";"
    | Let (t1, s1, e1, e2) -> t_exp_to_string t1 ^ " " ^ s1 ^ " = " ^ expr_to_string e1 ^ ";" ^ expr_to_string e2 
    | Assign (s1, e1) -> s1 ^ " = " ^ expr_to_string e1 
    | StateAssign (e1, s1, e2) -> expr_to_string e1 ^ "." ^ s1 ^ " = " ^ expr_to_string e2 ^ ";"
    | MapRead (e1, e2) -> expr_to_string e1 ^ "[" ^ expr_to_string e2 ^ "]"
    | MapWrite (e1, e2, e3) -> expr_to_string e1 ^ "[" ^ expr_to_string e2 ^ "]" ^ " = " ^ expr_to_string e3 
    | Call (_e1, _s1, _e2, _le) -> "Call"
    | CallTopLevel (_e1, _s1, _e2, _e3, _le) -> "CallTopLevel"
    | Revert -> "revert()"
    | If (e1, e2, e3) -> "if(" ^ expr_to_string e1 ^ ")" ^ " then " ^ expr_to_string e2 ^ " else " ^ expr_to_string e3 
    | Return (e1) -> "return " ^ expr_to_string e1
    | _ -> assert false


let function_to_string (func: fun_def) : string = "function " ^ func.name ^ "(" ^ 
    (List.fold_left (fun s (t_e, v) -> s ^ (t_exp_to_string t_e) ^ " " ^ v ^ ",") "" func.args) ^ "){" ^
    (expr_to_string func.body)
    ^ "}"
  
let contract_to_string (contract: contract_def) : string = 
  let (params, e) = contract.constructor in
  "contract " ^ contract.name ^ "{" ^ 
  (List.fold_left (fun s (t_e, v) -> s ^ (t_exp_to_string t_e) ^ " " ^ v ^ ";") "" contract.state) ^ 
  " constructor(" ^ (List.fold_left (fun s (t_e, v) -> s ^ (t_exp_to_string t_e) ^ " " ^ v ^ ",") "" params) ^ "){" ^
  (expr_to_string e) ^ "}" ^ (List.fold_left (fun s f -> s ^ (function_to_string f)) "" contract.functions)

  
  
let print_blockchain (blockchain: blockchain) _tbl : unit = 
  Hashtbl.iter (fun (c, a) (cname, sv, n) ->  match c, a, cname, sv, n with 
    | VContract(_), VAddress(_), s', sv', VUInt(_) -> 
      begin
        Format.eprintf "\n%s, %s, Contract Name: %s, State Variables: \n" (values_to_string c) (values_to_string a) s';
        StateVars.iter (fun k v -> Format.eprintf "%s ----> %s\n" k (expr_to_string v) ;) sv';
        Format.eprintf "Balance: %s\n" (values_to_string n);
      end
    | _ -> assert false
  ) blockchain



let print_contract_table (ct: contract_table) _tbl : unit = 
  Hashtbl.iter (fun k v -> match k, v with 
    | _s', {name = s1; state = s2; constructor = s3; functions = s4} -> 
      begin
        Format.eprintf "\nContract Name: %s" s1;
        Format.eprintf "\nState Variables: \n";
        List.iter (fun (t, s) -> Format.eprintf "%s ----> %s\n" s (t_exp_to_string t)) s2;
        Format.eprintf "\nConstructor: \n";
        List.iter (fun (t, s) -> Format.eprintf "%s ----> %s\n" s (t_exp_to_string t)) (fst s3);
        Format.eprintf "\nFunctions: \n";
        List.iter (fun {name = fname; args = fargs; rettype = t_e; body = fbody} -> 
          Format.eprintf "Function Name: %s\n" fname;
          Format.eprintf "Arguments: \n";
          List.iter (fun (t, s) -> Format.eprintf "%s ----> %s\n" s (t_exp_to_string t)) fargs;
          Format.eprintf "Return Type: %s\n" (t_exp_to_string t_e);
          Format.eprintf "Body: %s\n" (expr_to_string fbody);
        ) s4;
      end
  ) ct

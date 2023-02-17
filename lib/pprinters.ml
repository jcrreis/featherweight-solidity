open Types

let rec t_exp_to_string (t_e: t_exp) : string = match t_e with
| C n -> "contract(" ^ (Stdlib.string_of_int n) ^ ")"
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
  

let arit_op_to_string (a: arit_ops) : string =
  match a with 
    | Plus (_e1, _e2) -> "Plus"
    | Minus (_e1, _e2) -> "Minus"
    | Times (_e1, _e2) -> "Times"
    | Div (_e1, _e2) -> "Div"
    | Mod (_e1, _e2) -> "Mod"
    | Exp (_e1, _e2) -> "Exp"

let bool_op_to_string (b: bool_ops) : string = 
  match b with 
    | Conj (_e1, _e2) -> "And"
    | Disj (_e1, _e2) -> "Or"
    | Neg (_e1) -> "Not"
    | Equals (_e1, _e2) -> "Equals"
    | Lesser (_e1, _e2) -> "LessThan"
    | LesserOrEquals (_e1, _e2) -> "LessThanEq"
    | Greater (_e1, _e2) -> "GreaterThan"
    | GreaterOrEquals (_e1, _e2) -> "GreaterThanEq"
    | Inequals (_e1, _e2) -> "Inequals"
    

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
      | None -> "this."
      | Some s -> "this." ^s
    end
    | MsgSender -> "msg.sender"
    | MsgValue -> "msg.value"
    | Balance (e1) -> "Balance(" ^ expr_to_string e1 ^ ")"
    | Address (e1) -> "Address(" ^ expr_to_string e1 ^ ")"
    | StateRead (_e1, _s1) -> "StateRead"
    | Transfer (_e1, _e2) -> "Transfer"
    | New (_s1, _e1, _el1) -> "New"
    | Cons (_s1, _e1) -> "Cons"
    | Seq (_e1, _e2) -> "Seq"
    | Let (_t1, _s1, _e1, _e2) -> "Let"
    | Assign (_s1, _e1) -> "Assign"
    | StateAssign (_e1, _s1, _e2) -> "StateAssign"
    | MapRead (_e1, _e2) -> "MapRead"
    | MapWrite (_e1, _e2, _e3) -> "MapWrite"
    | Call (_e1, _s1, _e2, _le) -> "Call"
    | CallTopLevel (_e1, _s1, _e2, _e3, _le) -> "CallTopLevel"
    | Revert -> "Revert"
    | If (_e1, _e2, _e3) -> "If"
    | Return (_e1) -> "Return"
    | _ -> assert false

  
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

open Types

let rec t_exp_to_string (t_e: t_exp) : string = match t_e with
  | C (n) -> "contract" ^ "(" ^ n ^ ")"
  | Bool -> "boolean"
  | Unit -> "unit"
  | UInt -> "uint"
  | Address t -> begin match t with 
      | None -> "address"
      | Some t -> "address<" ^ t_exp_to_string t ^ ">"
    end
  | Map (t_e1, t_e2)-> "mapping(" ^ t_exp_to_string t_e1 ^ " => " ^ t_exp_to_string t_e2 ^ ")"
  | TRevert -> "revert"
  | Fun (lt_e, t_e) -> "Fun (" ^ (List.fold_left (fun s t_e -> s ^ t_exp_to_string t_e) "" lt_e) ^ ")" ^ " -> " ^ t_exp_to_string t_e
  | CTop -> "CTop"

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
  | VMapping (e1, _t_e) -> 
    (Hashtbl.fold (fun k v s -> match k, v with
         | Val(v1), Val(v2) -> s ^ values_to_string v1 ^ " ---> " ^ values_to_string v2 ^ "\n"
         | _ -> "erro") e1 "[ \n") ^ " ]"
  | VUnit -> ""

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
      | Some (s, _le) -> "this." ^ s
    end
  | MsgSender -> "msg.sender"
  | MsgValue -> "msg.value"
  | Balance (e1) -> "Balance(" ^ expr_to_string e1 ^ ")"
  | Address (e1) -> "Address(" ^ expr_to_string e1 ^ ")"
  | StateRead (e1, s1) -> expr_to_string e1 ^ "." ^ s1
  | Transfer (e1, e2) -> expr_to_string e1 ^ ".transfer(" ^ expr_to_string e2 ^ ")"
  | New (s1, e1, le) -> 
    let (_, print_args) = List.fold_left (fun (i, s) e  -> 
        (
          if i <> ((List.length le) - 1) then
            (i+1, s ^ (expr_to_string e) ^ ",")
          else
            (i+1, s ^ (expr_to_string e))
        )
      ) (0, "") le in 
    "new " ^ s1 ^ "(" ^ expr_to_string e1 ^ ")(" ^  print_args ^ ")"
  | Cons (s1, e1) -> s1 ^ "(" ^ expr_to_string e1 ^ ")"
  | Seq (e1, e2) -> "\n" ^ expr_to_string e1 ^ ";\n" ^ expr_to_string e2 ^ ";\n"
  | Let (t1, s1, e1, e2) -> t_exp_to_string t1 ^ " " ^ s1 ^ " = " ^ expr_to_string e1 ^ ";" ^ expr_to_string e2 
  | Assign (s1, e1) -> s1 ^ " = " ^ expr_to_string e1 
  | StateAssign (e1, s1, e2) -> expr_to_string e1 ^ "." ^ s1 ^ " = " ^ expr_to_string e2 ^ ";"
  | MapRead (e1, e2) -> expr_to_string e1 ^ "[" ^ expr_to_string e2 ^ "]"
  | MapWrite (e1, e2, e3) -> expr_to_string e1 ^ "[" ^ expr_to_string e2 ^ "]" ^ " = " ^ expr_to_string e3 
  | Call (e1, s1, e2, le) -> expr_to_string e1 ^ "." ^ s1 ^ ".value" ^ "(" ^ expr_to_string e2 ^ ")" 
                             ^ "." ^ List.fold_left (fun s e -> s ^ (expr_to_string e ) ^ ", ") "(" le ^ ")"
  | CallTopLevel (_e1, _s1, _e2, _e3, _le) -> "CallTopLevel"
  | Revert -> "revert()"
  | If (e1, e2, e3) -> "if(" ^ expr_to_string e1 ^ ")" ^ " then " ^ expr_to_string e2 ^ " else " ^ expr_to_string e3 
  | Return (e1) -> "return " ^ expr_to_string e1
  | _ -> "not applicable"

let function_to_string (func: fun_def) : string = "\nfunction " ^ func.name ^ "(" ^ 
                                                  (List.fold_left (fun s (t_e, v) -> s ^ (t_exp_to_string t_e) ^ " " ^ v ^ ",") "" func.args) ^ ")\n{\n" ^
                                                  (expr_to_string func.body)
                                                  ^ "\n}\n"

let contract_to_string (contract: contract_def) : string = 
  let (params, e) = contract.constructor in
  let super_contracts = match contract.super_contracts with
    | Class (_, sc) -> sc 
  in 
  "contract " ^ contract.name ^ " is " ^ List.fold_left (fun s (Class(c,_)) -> s ^ c ^ ", ") "" super_contracts ^ "\n{\n" ^ 
  (List.fold_left (fun s (t_e, v) -> s ^ (t_exp_to_string t_e) ^ " " ^ v ^ ";\n") "" contract.state) ^ 
  "\nconstructor(" ^ (List.fold_left (fun s (t_e, v) -> s ^ (t_exp_to_string t_e) ^ " " ^ v ^ ",") "" params) ^ "){\n" ^
  (expr_to_string e) ^ "\n}" ^ (List.fold_left (fun s f -> s ^ (function_to_string f)) "" contract.functions)



let print_blockchain (blockchain: blockchain) _tbl : unit = 
  let (contracts, accounts) = blockchain in
  Hashtbl.iter (fun (c, a) (cname, sv, n) ->  match c, a, cname, sv, n with 
      | VContract(_), VAddress(_), s', sv', VUInt(_) -> 
        begin
          Format.eprintf "\n%s, %s, Contract Name: %s, State Variables: \n" (values_to_string c) (values_to_string a) s';
          StateVars.iter (fun k v -> Format.eprintf "%s ----> %s\n" k (expr_to_string v) ;) sv';
          Format.eprintf "Balance: %s\n" (values_to_string n);
        end
      | _ -> assert false
    ) contracts
  ;
  Hashtbl.iter (fun a n ->  match a, n with 
      | VAddress _, VUInt _ -> 
        begin
          Format.eprintf "\nAccount: %s  ," (values_to_string a);
          Format.eprintf "Balance: %s\n" (values_to_string n);
        end
      | _ -> assert false
    ) accounts



let print_contract_table (ct: contract_table) _tbl : unit = 
  Hashtbl.iter (fun k v -> match k, v with 
      | _s', {name = s1; super_contracts = _s5 ; super_constructors_args = _s6; state = s2; constructor = s3; functions = s4; function_lookup_table = _s7} -> 
        begin
          Format.eprintf "\nContract Name: %s" s1;
          Format.eprintf "\nState Variables: \n";
          List.iter (fun (t, s) -> Format.eprintf "%s ----> %s\n" s (t_exp_to_string t)) s2;
          Format.eprintf "\nConstructor: \n";
          List.iter (fun (t, s) -> Format.eprintf "%s ----> %s\n" s (t_exp_to_string t)) (fst s3);
          Format.eprintf "\nFunctions: \n";
          List.iter (fun {name = fname; annotation = _annon; args = fargs; rettype = t_e; body = fbody} -> 
              Format.eprintf "Function Name: %s\n" fname;
              Format.eprintf "Arguments: \n";
              List.iter (fun (t, s) -> Format.eprintf "%s ----> %s\n" s (t_exp_to_string t)) fargs;
              Format.eprintf "Return Type: %s\n" (t_exp_to_string t_e);
              Format.eprintf "Body: %s\n" (expr_to_string fbody);
            ) s4;
        end
    ) ct
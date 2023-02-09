open Featherweightsolidity  
open Fs 


let fname = Sys.argv.(1)

let print_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Format.eprintf "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let rec values_to_string (v: values) : string =
  match v with 
    | VUInt (e1) -> string_of_int e1
    | VBool (e1) -> begin match e1 with 
      | True -> "true"
      | False -> "false"
    end
    | VAddress (e1) -> e1
    | VContract (e1) -> "Contract " ^ (string_of_int e1)
    | VMapping (e1, t_e) -> Hashtbl.fold (fun k v _s -> match k, v with
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
  

let rec expr_to_string (e: expr) tbl : string =
  match e with 
    | AritOp (a1) -> arit_op_to_string a1
    | BoolOp (b1) -> bool_op_to_string b1
    | Var (s1) -> 
      let v = Hashtbl.find tbl s1 in 
      expr_to_string v tbl
    | Val (v1) -> values_to_string v1
    | This (_s1) -> "This"
    | MsgSender -> "MsgSender"
    | MsgValue -> "MsgValue"
    | Balance (_e1) -> "Balance"
    | Address (e1) -> "Address"
    | StateRead (_e1, _s1) -> "StateRead"
    | Transfer (_e1, _e2) -> "Transfer"
    | New (_s1, _e1, _el1) -> "New"
    | Cons (_s1, _e1) -> "Cons"
    | Seq (_e1, _e2) -> "Seq"
    | Let (_t1, __s1, _e1, _e2) -> "Let"
    | Assign (__s1, _e1) -> "Assign"
    | StateAssign (_e1, _s1, _e2) -> "StateAssign"
    | MapRead (_e1, _e2) -> "MapRead"
    | MapWrite (_e1, _e2, _e3) -> "MapWrite"
    | Call (_e1, _s1, _e2, _le) -> "Call"
    | CallTopLevel (_e1, _s1, _e2, _e3, _le) -> "CallTopLevel"
    | Revert -> "Revert"
    | If (_e1, _e2, _e3) -> "If"
    | Return (_e1) -> "Return"
    | _ -> assert false

let rec t_exp_to_string (t_e: t_exp) : string = match t_e with
  | C n -> "contract(" ^ (Stdlib.string_of_int n) ^ ")"
  | Bool -> "boolean"
  | Unit -> "unit"
  | UInt -> "uint"
  | Address -> "address"
  | Map (t_e1, t_e2)-> "mapping(" ^ t_exp_to_string t_e1 ^ " => " ^ t_exp_to_string t_e2 ^ ")"
  | TRevert -> "revert"
  | Fun (lt_e, t_e) -> "Fun (" ^ (List.fold_left (fun s t_e -> s ^ t_exp_to_string t_e) "" lt_e) ^ ")" ^ " -> " ^ t_exp_to_string t_e

let print_blockchain (blockchain: blockchain) tbl : unit = 
  Hashtbl.iter (fun (c, a) (cname, sv, n) ->  match c, a, cname, sv, n with 
    | VContract(_), VAddress(_), s', sv', VUInt(_) -> 
      begin
        Format.eprintf "\n%s, %s, Contract Name: %s, State Variables: \n" (values_to_string c) (values_to_string a) s';
        StateVars.iter (fun k v -> Format.eprintf "%s ----> %s\n" k (expr_to_string v tbl) ;) sv';
        Format.eprintf "Balance: %s\n" (values_to_string n);
      end
    | _ -> assert false
  ) blockchain




  (* and contract_def = {
    name : string;
    state : (t_exp * string) list;
    constructor : (t_exp * string) list * expr;
    functions : fun_def list;
  }
  
  
  
  type contract_table = (string, contract_def) Hashtbl.t *)

let print_contract_table (ct: contract_table) tbl : unit = 
  Hashtbl.iter (fun k v -> match k, v with 
    | s', {name = s1; state = s2; constructor = s3; functions = s4} -> 
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
          Format.eprintf "Body: %s\n" (expr_to_string fbody tbl);
        ) s4;
      end
  ) ct


let () =
  let cin = open_in fname in
  let lexbuf = Lexing.from_channel cin in
  try
    let e: expr = Parser.prog Lexer.read lexbuf in
    let ct: contract_table = Hashtbl.create 64 in
    let blockchain: blockchain = Hashtbl.create 64 in
    let sigma: values Stack.t = Stack.create() in
    let conf: conf = (blockchain, blockchain, sigma, e) in
    let vars: (string, expr) Hashtbl.t = Hashtbl.create 64 in
    let _p: program = (ct, blockchain, e) in
    (* ADD CONTRACTS TO CONTRACT TABLE *)
    Hashtbl.add ct "Bank" (bank_contract());
    Hashtbl.add ct "BloodBank" (blood_bank_contract());
    Hashtbl.add ct "Donor" (donor_contract());
    Hashtbl.add ct "EOAContract" (eoa_contract());
    let (_, _, _, ppx) = eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus(AritOp(Div(Val(VUInt 1),Val(VUInt 0))), Val(VUInt 2))))) in 
    Format.eprintf "%s" (expr_to_string ppx vars);

    let (blockchain, _blockchain', _sigma, res) = eval_expr ct vars conf in
    Format.eprintf "Contract Table: @.";
    print_contract_table ct vars;
    Format.eprintf "Blockchain: @.";
    print_blockchain blockchain vars;
    match res with 
      | Revert -> Format.eprintf "Revert@."
      | _ -> Format.eprintf "Result: %s@." (expr_to_string res vars)
  with Parser.Error ->
    Format.eprintf "Syntax error@.";
    print_position lexbuf;
    Format.eprintf "@."

(* let () =  (* let x: int = 10 ; x + x ;*)
(* let e1 = (AritOp(Plus(Num(1),Times(Num(2),Num(3))))) in
   Format.eprintf "%s\n" (arit_op_to_string e1); *)
let ct: contract_table = Hashtbl.create 64 in
let blockchain: blockchain = Hashtbl.create 64 in
let sigma: values Stack.t = Stack.create() in
let conf: conf = (blockchain, blockchain, sigma, Val(VUInt(0))) in
let vars: (string, expr) Hashtbl.t = Hashtbl.create 64 in
(* let p : program = (ct, blockchain, Val(VUInt(0))) in *)

let print_set s = FV.iter print_endline s in
let e2 = New("BloodBank", Val(VUInt(0)),[Val(VMapping(Hashtbl.create 64)); Val(VAddress("0x000x"));Val(VUInt(1111))]) in
let lst = free_addr_names e2 in
print_set lst;
(* let e1 = BoolOp(Equals((AritOp(Plus(Val (VUInt(1)),AritOp(Plus(Val(VUInt(10)),(Val(VUInt(1)))))))),Val(VUInt(13)))) in *)
(* let (_, _, _, Val(VBool(b))) = eval_expr ct vars (blockchain, blockchain, sigma, e1) in
   match b with 
   | True -> Format.eprintf "True";
   | False -> Format.eprintf "False";
   | _ -> (); *)
(* Format.eprintf "%d\n" i; *)
Hashtbl.add ct "Bank" (bank_contract());
Hashtbl.add ct "BloodBank" (blood_bank_contract());
Hashtbl.add ct "Donor" (donor_contract());
Hashtbl.add ct "EOAContract" (eoa_contract());
Hashtbl.add blockchain (VContract 0, VAddress "0x0000000000000000000000000000000000000000") ("EOAContract", StateVars.empty, VUInt(0));
Hashtbl.add blockchain (VContract 1, VAddress "0x00") ("EOAContract", StateVars.empty, VUInt(1000000000));
let res = state_vars_contract "Bank" ct in
let res2 = state_vars_contract "BloodBank" ct in
let res3 = state_vars_contract "Donor" ct in
(* let res4 = state_vars_contract "Error" ct in  *)
print_tuples res;
print_tuples res2;
print_tuples res3;
(* print_tuples res4; *)
let (res1, _) = function_body "Bank" "transfer" [Val(VUInt(1));Val(VUInt(1))] ct in
print_tuples res1;
(* print_tuples [(res, "transfer fun return_type")]; *)
let address = generate_new_ethereum_address() in 
Format.eprintf "\n%s" address;
Format.eprintf "\n%d\n" ((Bytes.length (Bytes.of_string address))*8);
Stack.push (VAddress "0x00") sigma;
let res = eval_expr ct vars (blockchain, blockchain, sigma, e2) in 
match res with 
| (_, _, _, Revert) -> Format.eprintf "\n%s" "REVERTED" ; 
| _ -> Format.eprintf "\n%s" "SUCESSO"; *)


  (* print_tuples [(res, "isHealty fun return_type")] *)

  (* match e2 with
     | Val (VUInt(i)) -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
     | _ -> assert false *)

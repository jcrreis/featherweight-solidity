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
    | VMapping (e1) -> Hashtbl.fold (fun k v s -> match k, v with
      | Val(v1), Val(v2) -> values_to_string v1 ^ " -> " ^ values_to_string v2
      | _ -> assert false) e1 ""
    | VUnit -> "Unit"

let arit_op_to_string (a: arit_ops) : string =
  match a with 
    | Plus (e1, e2) -> "Plus"
    | Minus (e1, e2) -> "Minus"
    | Times (e1, e2) -> "Times"
    | Div (e1, e2) -> "Div"
    | Mod (e1, e2) -> "Mod"
    | Exp (e1, e2) -> "Exp"

let bool_op_to_string (b: bool_ops) : string = 
  match b with 
    | Conj (e1, e2) -> "And"
    | Disj (e1, e2) -> "Or"
    | Neg (e1) -> "Not"
    | Equals (e1, e2) -> "Equals"
    | Lesser (e1, e2) -> "LessThan"
    | LesserOrEquals (e1, e2) -> "LessThanEq"
    | Greater (e1, e2) -> "GreaterThan"
    | GreaterOrEquals (e1, e2) -> "GreaterThanEq"
    | Inequals (e1, e2) -> "Inequals"
  

let expr_to_string (e: expr) : string =
  match e with 
    | AritOp (a1) -> arit_op_to_string a1
    | BoolOp (b1) -> bool_op_to_string b1
    | Var (s1) -> s1
    | Val (v1) -> values_to_string v1
    | This (s1) -> "This"
    | MsgSender -> "MsgSender"
    | MsgValue -> "MsgValue"
    | Balance (e1) -> "Balance"
    | Address (e1) -> "Address"
    | StateRead (e1, s1) -> "StateRead"
    | Transfer (e1, e2) -> "Transfer"
    | New (s1, e1, el1) -> "New"
    | Cons (s1, e1) -> "Cons"
    | Seq (e1, e2) -> "Seq"
    | Let (t1, s1, e1, e2) -> "Let"
    | Assign (s1, e1) -> "Assign"
    | StateAssign (e1, s1, e2) -> "StateAssign"
    | MapRead (e1, e2) -> "MapRead"
    | MapWrite (e1, e2, e3) -> "MapWrite"
    | Call (e1, s1, e2, le) -> "Call"
    | CallTopLevel (e1, s1, e2, e3, le) -> "CallTopLevel"
    | Revert -> "Revert"
    | If (e1, e2, e3) -> "If"
    | Return (e1) -> "Return"
    | _ -> assert false


let print_blockchain (blockchain: blockchain) : unit = 
  Hashtbl.iter (fun (c, a) (cname, sv, n) ->  match c, a, cname, sv, n with 
    | VContract(_), VAddress(_), s', sv', VUInt(_) -> 
      begin
        Format.eprintf "\n%s, %s, Contract Name: %s, State Variables: \n" (values_to_string c) (values_to_string a) s';
        StateVars.iter (fun k v -> Format.eprintf "%s ----> %s\n" k (expr_to_string v) ;) sv';
        Format.eprintf "Balance: %s\n" (values_to_string n);
      end
    | _ -> assert false
  ) blockchain

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
    let p: program = (ct, blockchain, e) in
    (* ADD CONTRACTS TO CONTRACT TABLE *)
    Hashtbl.add ct "bank" (bank_contract());
    Hashtbl.add ct "bloodbank" (blood_bank_contract());
    Hashtbl.add ct "donor" (donor_contract());
    Hashtbl.add ct "eoacontract" (eoa_contract());

    let (blockchain, blockchain', sigma, res) = eval_expr ct vars conf in
    print_blockchain blockchain;
    match res with 
    | Revert -> Format.eprintf "Revert@."
    | _ -> Format.eprintf "Result: %s@." (expr_to_string res)
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

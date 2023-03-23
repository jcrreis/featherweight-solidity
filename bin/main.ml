open Featherweightsolidity  
open Fs 
open Types
open Pprinters
open Contracts
open Typechecker 
open Utils
open C3 

let fname = Sys.argv.(1)

let print_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Format.eprintf "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let wikipedia_example_c3_linearization ct = 
  (*https://en.wikipedia.org/wiki/C3_linearization*)
  Hashtbl.add ct "C" {name="C"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "B" {name="B"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "A" {name="A"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "D" {name="D"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "E" {name="E"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "K1" {name="K1"; super_contracts=["C";"A";"B"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "K3" {name="K3"; super_contracts=["A";"D"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "K2" {name="K2"; super_contracts=["B";"D";"E"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "Z" {name="Z"; super_contracts=["K1";"K3";"K2"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};

  let l = c3_linearization "Z" ct in
  Format.eprintf "[";
  List.iter (fun x -> Format.eprintf "%s," x) l;
  Format.eprintf "]\n"

let test_python_mro_example ct = 
  (*https://www.python.org/download/releases/2.3/mro/*)
  Hashtbl.add ct "C" {name="C"; super_contracts=["D"; "F"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "B" {name="B"; super_contracts=["E"; "D"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "A" {name="A"; super_contracts=["B"; "C"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "D" {name="D"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "E" {name="E"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "F" {name="F"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};

  let l = c3_linearization "A" ct in
  Format.eprintf "[";
  List.iter (fun x -> Format.eprintf "%s," x) l;
  Format.eprintf "]\n"

let deposit ct vars b b' s n sender contract = 
  let conf = (b, b', s,  CallTopLevel(contract, "deposit", Val(VUInt n), Val(sender), [])) in 
  eval_expr ct vars conf 

let transfer ct vars b b' s n sender receiver contract = 
  let conf = (b, b', s,  CallTopLevel(contract, "transfer", Val(VUInt 0), Val(sender), [Val(receiver);Val(VUInt n)])) in 
  eval_expr ct vars conf 

let withdraw ct vars b b' s n sender contract = 
  let conf = (b, b', s, CallTopLevel(contract, "withdraw", Val(VUInt 0), Val(sender), [Val(VUInt n)])) in  
  eval_expr ct vars conf 

let get_balance ct vars b b' s sender contract =
  let conf = (b, b', s, CallTopLevel(contract, "getBalance", Val (VUInt 0), Val (sender), [])) in 
  eval_expr ct vars conf 

let get_liquidity ct vars b b' s sender contract = 
  let conf = (b, b', s, CallTopLevel(contract, "executeLiquidity", Val (VUInt 0), Val (sender), [])) in 
  eval_expr ct vars conf

let () =
  let cin = open_in fname in
  let lexbuf = Lexing.from_channel cin in
  try
    let e: expr = Parser.prog Lexer.read lexbuf in
    let ct: contract_table = Hashtbl.create 64 in
    let blockchain: blockchain = Hashtbl.create 64 in
    let sigma: values Stack.t = Stack.create() in
    let _conf: conf = (blockchain, blockchain, sigma, e) in
    let vars: (string, expr) Hashtbl.t = Hashtbl.create 64 in
    let _p: program = (ct, blockchain, e) in
    (* ADD CONTRACTS TO CONTRACT TABLE *)
    (* Hashtbl.add ct "Bank" (bank_contract());
       Hashtbl.add ct "BloodBank" (blood_bank_contract());
       Hashtbl.add ct "Donor" (donor_contract());
       Hashtbl.add ct "EOAContract" (eoa_contract()); *)
    (* Hashtbl.add ct "Bank" (bank_contract()); *)
    (*https://github.com/federicobond/c3-linearization*)
    wikipedia_example_c3_linearization ct; 
    test_python_mro_example ct;
    Hashtbl.add ct "EOAContract" (eoa_contract());
    Hashtbl.add ct "Bank" (bank_contract());
    Hashtbl.add ct "SimpleBank" (simple_bank_contract());
    Hashtbl.add ct "BankWithDepositTracker" (bank_with_deposit_tracker_contract());
    let e = New("EOAContract", Val(VUInt 10000), []) in 
    Format.eprintf "\n%s\n" (expr_to_string e);
    let conf = (blockchain, blockchain, sigma, e) in 
    let (blockchain, blockchain', sigma, res) = eval_expr ct vars conf in
    let a1 = match eval_expr ct vars (blockchain, blockchain', sigma, Address(res)) with 
      | (_, _, _, Val (VAddress a)) -> VAddress a
      | _ -> assert false
    in 
    let (blockchain, blockchain', sigma, res) = eval_expr ct vars conf in
    let a2 = match eval_expr ct vars (blockchain, blockchain', sigma, Address(res)) with 
      | (_, _, _, Val (VAddress a)) -> VAddress a
      | _ -> assert false
    in 
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result: %s@." (expr_to_string res);
      Format.eprintf "Blockchain: @.";
      print_blockchain blockchain vars;
    let e = New("BankWithDepositTracker", Val(VUInt 0), []) in 
    let conf = (blockchain, blockchain', sigma, e) in 
    let (blockchain, blockchain', sigma, contract) = eval_expr ct vars conf in
    match contract with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result: %s@." (expr_to_string contract);
      Format.eprintf "Blockchain: @.";
      print_blockchain blockchain vars;
    Format.eprintf "\n%s\n" (contract_to_string ((Hashtbl.find ct "Bank")));
    let (blockchain, blockchain', sigma, res) = deposit ct vars blockchain blockchain' sigma 564 a1 contract in
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result: %s@." (expr_to_string res);
      print_blockchain blockchain vars;
    let (blockchain, _blockchain', _sigma, res) = withdraw ct vars blockchain blockchain' sigma 200 a1 contract in 
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result: %s@." (expr_to_string res);
      print_blockchain blockchain vars;
    let (blockchain, _blockchain', _sigma, res) = transfer ct vars blockchain blockchain' sigma 364 a1 a2 contract in 
      match res with 
      | Revert -> Format.eprintf "Revert@.";
      | _ -> Format.eprintf "Result: %s@." (expr_to_string res);
        print_blockchain blockchain vars;
    let (blockchain, blockchain', sigma, res) = deposit ct vars blockchain blockchain' sigma 564 a1 contract in
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result: %s@." (expr_to_string res);
    let (blockchain, blockchain', sigma, res) = get_balance ct vars blockchain blockchain' sigma a1 contract in
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result get balance A1: %s@." (expr_to_string res);
    let (blockchain, _blockchain', _sigma, res) = get_liquidity ct vars blockchain blockchain' sigma a2 contract in
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "Result Liquidity: %s@." (expr_to_string res);
    print_blockchain blockchain vars;

    Format.eprintf "%s" (contract_to_string (blood_bank_contract()));
    Format.eprintf "%s" (contract_to_string (donor_contract()));
      (* let s = read_whole_file "./contracts/bank.sol" in
         Format.eprintf "%s\n" (encode_contract s); *)
      (* let (_, _, _, e1) = eval_expr ct vars (blockchain, blockchain, sigma, AritOp(Minus(Val(VUInt 2), Val(VUInt 3)))) in
         Format.eprintf "\n RESULTADO:  %s" (expr_to_string e1);  *)
      (* Format.eprintf "\n%s\n" (encode_contract (contract_to_string (donor_contract()))); *)
      (* let (blockchain, _blockchain', _sigma, res) = eval_expr ct vars conf in *)
      (* Format.eprintf "Contract Table: @.";
         print_contract_table ct vars; *)
      (* Format.eprintf "Blockchain: @.";
         print_blockchain blockchain vars; *)
      let gamma = (Hashtbl.create 64) in 
      let c1 = get_contract_by_address blockchain a1 in 
      let c2 = get_contract_by_address blockchain a2 in  
      let (c1name, _, _) = Hashtbl.find blockchain (c1, a1) in 
      let (c2name, _, _ ) = Hashtbl.find blockchain (c2, a2) in 
      let t_a: t_exp = Address (C c1name) in 
      let t_a': t_exp = Address (C c2name) in 
      Hashtbl.add gamma (Val a1) (t_a);
      Hashtbl.add gamma (Val a2) (t_a');
      (* a1 e a2 tem tipo EOAContract..... deviam pertencer ao mesmo tipo?*)
      typecheck gamma (MsgSender) (Address CTop) ct blockchain;
      typecheck gamma (Val a1) (Address (C "EOAContract")) ct blockchain;
      typecheck gamma (Val a2) (Address (C "EOAContract")) ct blockchain;
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

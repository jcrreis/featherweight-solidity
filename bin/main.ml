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

let _wikipedia_example_c3_linearization ct = 
  (*https://en.wikipedia.org/wiki/C3_linearization*)
  Hashtbl.add ct "C" {name="C"; super_contracts=Class("C",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64};
  Hashtbl.add ct "B" {name="B"; super_contracts=Class("B",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "A" {name="A"; super_contracts=Class("A",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "D" {name="D"; super_contracts=Class("D",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "E" {name="E"; super_contracts=Class("E",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  let k1 = Class("K1",[Class("C",[]);Class("A",[]);Class("B",[])]) in 
  let k3 = Class("K3",[Class("A",[]);Class("D",[])]) in 
  let k2 = Class("K2",[Class("B",[]);Class("D",[]);Class("E",[])]) in 
  Hashtbl.add ct "K1" {name="K1"; super_contracts=k1; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "K3" {name="K3"; super_contracts=k3; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "K2" {name="K2"; super_contracts=k2; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "Z" {name="Z"; super_contracts=Class("Z", [k1; k3; k2]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};

  let l = match c3_linearization (Hashtbl.find ct "Z") with 
    | Ok v -> v 
    | _ -> assert false
  in 
  Format.eprintf "[";
  List.iter (fun x -> Format.eprintf "%s," x) l;
  Format.eprintf "]\n"

let _test_python_mro_example ct = 
  (*https://www.python.org/download/releases/2.3/mro/*)
  Hashtbl.add ct "C" {name="C"; super_contracts=Class("C", [Class("D",[]); Class("F", [])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "B" {name="B"; super_contracts=Class("B", [Class("E",[]); Class("D", [])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "A" {name="A"; super_contracts=Class("C", [Class("B", [Class("E",[]); Class("D", [])]);Class("C", [Class("D",[]); Class("F", [])])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "D" {name="D"; super_contracts=Class("D",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "E" {name="E"; super_contracts=Class("E",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "F" {name="F"; super_contracts=Class("F",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};

  let l = match c3_linearization (Hashtbl.find ct "A") with 
    | Ok v -> v
    | _ -> assert false 
  in 
  Format.eprintf "[";
  List.iter (fun x -> Format.eprintf "%s," x) l;
  Format.eprintf "]\n"


(* let _test_fail_mro = 
  (*https://www.python.org/download/releases/2.3/mro/*)
  let ct: contract_table = Hashtbl.create 64 in
  Hashtbl.replace ct "C" {name="C"; super_contracts=Class("C", [Class("A",[]); Class("B", [])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.replace ct "B" {name="B"; super_contracts=Class("B", [Class("A",[]);Class("C",[])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.replace ct "A" {name="A"; super_contracts=Class("A", [Class("C",[])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};


  let l = match c3_linearization (Hashtbl.find ct "C") with 
    | Ok v -> v
    | Error s -> raise (NoLinearization s)
  in 
  Format.eprintf "$[";
  List.iter (fun x -> Format.eprintf "%s," x) l;
  Format.eprintf "]$\n" *)


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

let transferTo ct vars b b' s n wallet_address sender contract = 
  let conf = (b, b', s, CallTopLevel(contract, "transferTo", Val (VUInt 0), Val (sender), [
      wallet_address; Val (VUInt n) 
    ])) in 
  eval_expr ct vars conf


let add_contract_to_contract_table contract ct = 
  let linearization: string list = match c3_linearization contract with 
    | Ok v -> v 
    | _ -> assert false  
  in 
  List.iter (fun s -> Format.eprintf "%s" s) linearization;
  let contracts_hierarchy = (List.map (fun cname -> 
      if cname = contract.name then contract else 
        Hashtbl.find ct cname) linearization) in
  let method_table = Hashtbl.create 64 in 
  let method_table = List.fold_left (fun tbl (c_def: contract_def) -> 
      let functions = c_def.functions in 
      let tbl = List.fold_left (fun tbl (f: fun_def) -> 
          if Hashtbl.mem tbl f.name then tbl else (Hashtbl.add tbl f.name f;tbl)
        ) tbl functions
      in 
      tbl 
    ) method_table contracts_hierarchy
  in 
  let contract: contract_def = {
    name = contract.name;
    super_contracts = contract.super_contracts;
    super_constructors_args = contract.super_constructors_args;  
    state = contract.state; 
    constructor = contract.constructor;
    functions = contract.functions;
    function_lookup_table = method_table;
  }
  in 
  Hashtbl.add ct contract.name contract ; ct 


let _bank_example ct vars blockchain sigma =
  let ct = add_contract_to_contract_table (bank_contract()) ct in 
  let ct = add_contract_to_contract_table (simple_bank_contract()) ct in 
  let ct = add_contract_to_contract_table (bank_with_deposit_tracker_contract()) ct in 
  let a1 = (VAddress (generate_new_ethereum_address())) in
  let a2 = (VAddress (generate_new_ethereum_address())) in  
  let (_contracts, accounts) = blockchain in  
  Hashtbl.add accounts a1 (VUInt 100000); 
  Hashtbl.add accounts a2 (VUInt 100000);  
  print_blockchain blockchain vars;
  let e = New("BankWithDepositTracker", Val(VUInt 0), []) in 
  let conf = (blockchain, blockchain, sigma, e) in 
  let (blockchain, blockchain', sigma, contract) = eval_expr ct vars conf in
  match contract with 
  | Revert -> Format.eprintf "Revert@.";
  | _ -> Format.eprintf "Result: %s@." (expr_to_string contract);
    Format.eprintf "Blockchain: @.";
    print_blockchain blockchain vars;
    Format.eprintf "\n%s\n" (contract_to_string ((Hashtbl.find ct "Bank")));
    let (blockchain, blockchain', sigma, res) = deposit ct vars blockchain blockchain' sigma 564 a1 contract in
    match res with 
    | Revert -> Format.eprintf "Revert1123@.";
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

                let (_contracts, _accounts) = blockchain in
                let gamma = (Hashtbl.create 64, Hashtbl.create 64, Hashtbl.create 64 ) in 
                typecheck gamma (MsgSender) (Address (Some CTop)) ct blockchain


let wallet_example ct vars blockchain sigma = 
  let ct = add_contract_to_contract_table (wallet_contract()) ct in 
  let a1 = (VAddress (generate_new_ethereum_address())) in
  let a2 = (VAddress (generate_new_ethereum_address())) in  
  let (_contracts, accounts) = blockchain in  
  Hashtbl.add accounts a1 (VUInt 100000); 
  Hashtbl.add accounts a2 (VUInt 100000);  
  let e = New("Wallet", Val(VUInt 10000), []) in
  Stack.push a1 sigma;
  let (blockchain, blockchain', sigma, contract) = eval_expr ct vars (blockchain, blockchain, sigma, e) in 
  let e = New("Wallet", Val(VUInt 0), []) in
  Stack.push a2 sigma;
  let (blockchain, blockchain', sigma, contract2) = eval_expr ct vars (blockchain, blockchain', sigma, e) in 
  let (blockchain, blockchain', sigma, res) = get_balance ct vars blockchain blockchain' sigma a1 contract in
  match res with 
  | Revert -> Format.eprintf "Revert@.";
  | _ -> Format.eprintf "Result get balance: %s@." (expr_to_string res);
    (* ct vars b b' s n sender contract *)
    let (blockchain, blockchain', sigma, res) = deposit ct vars blockchain blockchain' sigma 10000 a1 contract in
    match res with 
    | Revert -> Format.eprintf "Revert@.";
    | _ -> Format.eprintf "%s@." (expr_to_string res);
      let (_blockchain, _blockchain', _sigma, res) = withdraw ct vars blockchain blockchain' sigma 850 a1 contract in
      match res with 
      | Revert -> Format.eprintf "Revert@.";
      | _ -> Format.eprintf "%s@." (expr_to_string res);
        (* let _transferTo ct vars b b' s n wallet_address sender contract  *)
        let (blockchain, blockchain', sigma, res) = withdraw ct vars blockchain blockchain' sigma 850 a1 contract in
        match res with 
        | Revert -> Format.eprintf "Revert@.";
        | _ -> Format.eprintf "%s@." (expr_to_string res);
          let (blockchain, blockchain', sigma, res) = eval_expr ct vars (blockchain, blockchain', sigma, (Address(contract2))) in
          match res with 
          | Revert -> Format.eprintf "Revert@.";
          | _ -> Format.eprintf "%s@." (expr_to_string res);
            let (_blockchain, _blockchain', _sigma, res) = transferTo ct vars blockchain blockchain' sigma 850 ((Address(contract2))) a1 contract in
            match res with 
            | Revert -> Format.eprintf "Revert@.";
            | _ -> Format.eprintf "%s@." (expr_to_string res);
              Format.eprintf "======================================";
              print_blockchain blockchain vars

let typecheck_contract (g: gamma) (c: contract_def) (ct: contract_table) (b: blockchain) : unit = 
  let typecheck_constructor (g: gamma) (constructor: (t_exp * string) list * expr) (ct: contract_table) (b: blockchain) : unit = 
    let (gv, ga, gc) = g in
    let (args, body) = constructor in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (args);
    typecheck (gv, ga, gc) body Unit ct b; 
  in 
  let typecheck_function (g: gamma) (f: fun_def) (ct: contract_table) (b: blockchain): unit =
    let (gv, ga, gc) = g in 
    let rettype: t_exp = f.rettype in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (f.args);
    typecheck (gv, ga, gc) (f.body) rettype ct b;
  in 
  let (gv, ga, gc) = g in 
  Hashtbl.add gv "this" (C c.name);
  Hashtbl.add gv "msg.sender" (Address None);
  Hashtbl.add gv "msg.value" (UInt);
  List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (c.state);
  typecheck_constructor (gv, ga, gc) c.constructor ct b;     
  List.iter (fun (f_def: fun_def) -> Format.eprintf "%s" f_def.name; typecheck_function (gv, ga, gc) f_def ct b) (c.functions);
  Format.eprintf "\nContrato Validado com Sucesso!!\n"

let () =
  let cin = open_in fname in
  let lexbuf = Lexing.from_channel cin in
  try
    let e: expr = Parser.prog Lexer.read lexbuf in
    let ct: contract_table = Hashtbl.create 64 in
    let blockchain: blockchain = (Hashtbl.create 64, Hashtbl.create 64) in
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
    (* wikipedia_example_c3_linearization ct; 
    test_python_mro_example ct;
    test_fail_mro; Ver porque não retorna erro *)
    (* if false then 
      bank_example ct vars blockchain sigma; *)
  if false then 
    wallet_example ct vars blockchain sigma;
  let gamma: gamma = (Hashtbl.create 64, Hashtbl.create 64, Hashtbl.create 64) in
  typecheck gamma (Val(VUInt 2)) UInt ct blockchain;
  typecheck gamma (AritOp(Plus(Val(VUInt 2),Val(VUInt 2)))) UInt ct blockchain;
  (* typecheck gamma (MsgSender) (Address None) ct blockchain;
  typecheck gamma (MsgSender) (Address (Some (C "1"))) ct blockchain; *)
  (* let e1 : expr = Let(Address (Some (C "Bank")), "x", Val(VUInt 2), Val(VUInt 3)) in 
  typecheck gamma e1 UInt ct blockchain; *)
  Hashtbl.add ct "C" {name="C"; super_contracts=Class("C", [Class("D",[]); Class("F", [])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "B" {name="B"; super_contracts=Class("B", [Class("E",[]); Class("D", [])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "A" {name="A"; super_contracts=Class("C", [Class("B", [Class("E",[]); Class("D", [])]);Class("C", [Class("D",[]); Class("F", [])])]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "D" {name="D"; super_contracts=Class("D",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "E" {name="E"; super_contracts=Class("E",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};
  Hashtbl.add ct "F" {name="F"; super_contracts=Class("F",[]); super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]; function_lookup_table = Hashtbl.create 64;};

  let (gv, ga, gc) = gamma in 
  Hashtbl.add gc (VContract 1) (C "B");  
  (* let e1 : expr = Let(Address (Some (C "B")), "x", Address(Val(VContract 1)), Val(VUInt 2)) in  *)
  let e1 : expr = Let(C "B", "x", Val(VContract 1), Val(VUInt 2)) in 
  Hashtbl.iter (fun k v -> Format.eprintf "%s" ((values_to_string k) ^ " value " ^ (t_exp_to_string v));) gc;
  
  typecheck (gv, ga, gc) e1 UInt ct blockchain; 
  let gamma: gamma = (Hashtbl.create 64, Hashtbl.create 64, Hashtbl.create 64) in
  Hashtbl.add ct "Wallet" (wallet_contract());
  Hashtbl.add ct "Bank" (bank_contract());
  typecheck_contract gamma (wallet_contract()) ct blockchain;
  typecheck_contract gamma (bank_contract()) ct blockchain
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

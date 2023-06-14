open Featherweightsolidity  
open Fs 
open Types
open Pprinters
(* open Contracts *)
open Typechecker  
open Utils
open C3 



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
  let conf = (b, b', s,  CallTopLevel(contract, "transferTo", Val(VUInt 0), Val(sender), [Val(receiver);Val(VUInt n)])) in 
  eval_expr ct vars conf 

let withdraw ct vars b b' s n sender contract = 
  let conf = (b, b', s, CallTopLevel(contract, "withdraw", Val(VUInt 0), Val(sender), [Val(VUInt n)])) in  
  eval_expr ct vars conf 

let get_balance ct vars b b' s sender contract =
  let conf = (b, b', s, CallTopLevel(contract, "getBalance", Val (VUInt 0), Val (sender), [])) in 
  eval_expr ct vars conf 

let get_liquidity ct vars b b' s sender contract = 
  let conf = (b, b', s, CallTopLevel(contract, "getLiquidity", Val (VUInt 0), Val (sender), [])) in 
  eval_expr ct vars conf

let transferTo ct vars b b' s n wallet_address sender contract = 
  let conf = (b, b', s, CallTopLevel(contract, "transferTo", Val (VUInt 0), Val (sender), [
      wallet_address; Val (VUInt n) 
    ])) in 
  eval_expr ct vars conf


let bank_example ct vars blockchain sigma =
  let a1 = (VAddress (generate_new_ethereum_address())) in
  let a2 = (VAddress (generate_new_ethereum_address())) in  
  let (_contracts, accounts) = blockchain in  
  Hashtbl.add accounts a1 (VUInt 10000); 
  Hashtbl.add accounts a2 (VUInt 100000);  
  print_blockchain blockchain vars;
  let e = New("Bank", Val(VUInt 0), []) in 
  let conf = (blockchain, blockchain, sigma, e) in 
  let (blockchain, blockchain', sigma, contract) = eval_expr ct vars conf in
  match contract with 
  | Revert -> Format.eprintf "Revert@.";
  | _ ->
    Format.eprintf "Blockchain: @.";
    print_blockchain blockchain vars;
    let (_blockchain, _blockchain', _sigma, res) = deposit ct vars blockchain blockchain' sigma 564 a1 contract in
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
              | Revert -> Format.eprintf "Revert13231@.";
              | _ -> Format.eprintf "Result Liquidity: %s@." (expr_to_string res);
                print_blockchain blockchain vars


let wallet_example ct vars blockchain sigma = 
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

let inheritance_example ct vars blockchain sigma = 
  let a1 = (VAddress (generate_new_ethereum_address())) in
  let a2 = (VAddress (generate_new_ethereum_address())) in
  let (_contracts, accounts) = blockchain in  
  Hashtbl.add accounts a1 (VUInt 100000); 
  Hashtbl.add accounts a2 (VUInt 100000);
  Stack.push a1 sigma;
  let e = New("B", Val(VUInt 10000), [Val(VUInt 10)]) in
  let (blockchain, blockchain', sigma, contract) = eval_expr ct vars (blockchain, blockchain, sigma, e) in 
  let (_, _, _, res) = eval_expr ct vars (blockchain, blockchain', sigma, CallTopLevel(contract, "getCounter", Val (VUInt 0), Val (a1), [])) in
  Format.eprintf "%s@." (expr_to_string res)

let rec parse_file fname ct blockchain blockchain' sigma vars =
  let print_position lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    Format.eprintf "%s:%d:%d" pos.pos_fname
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  in

  let cin = open_in fname in
  let lexbuf = Lexing.from_channel cin in
  try
    let (imports, e) : (string list * expr) = Parser.prog Lexer.read lexbuf in
    (* replace the first dot, for dir name example: ./Donor.sol => contracts/Donor.sol*)
    let r = Str.regexp "." in 
    let imports = List.map (fun x -> (Str.replace_first r (Filename.dirname fname) x) ) imports in 
    let (ct, blockchain, blockchain', sigma, vars) = List.fold_left 
        (fun (ct, blockchain, blockchain', sigma, vars) x -> parse_file x ct blockchain blockchain' sigma vars) (ct, blockchain, blockchain', sigma, vars) imports in 
    let (blockchain, blockchain', sigma, _) = eval_expr ct vars (blockchain, blockchain', sigma, e) in
    (ct, blockchain, blockchain', sigma, vars)
  with Parser.Error ->
    Format.eprintf "Syntax error@.";
    print_position lexbuf;
    Format.eprintf "@.";
    (ct, blockchain, blockchain', sigma, vars)


let () =
  let fname = Sys.argv.(1) in 

  (* let cin = open_in fname in
     let lexbuf = Lexing.from_channel cin in *)
  (* let (_imports, e) : (string list * expr) = Parser.prog Lexer.read lexbuf in *)
  (* parse_file fname; *)
  (* let e : expr = Parser.prog Lexer.read lexbuf in *)

  let ct: contract_table = Hashtbl.create 64 in
  let blockchain: blockchain = (Hashtbl.create 64, Hashtbl.create 64) in
  let sigma: values Stack.t = Stack.create() in
  (* let conf: conf = (blockchain, blockchain, sigma, e) in *)
  let vars: (string, expr) Hashtbl.t = Hashtbl.create 64 in
  let gamma: gamma = (Hashtbl.create 64, Hashtbl.create 64, Hashtbl.create 64, Hashtbl.create 64) in
  (* let _p: program = (ct, blockchain, e) in
     let _ = eval_expr ct vars conf in 
     let cname = match e with 
     | AddContract cdef -> Format.eprintf "%s" (contract_to_string cdef);cdef.name
     | _ -> assert false 
     in *)

  (* Hashtbl.iter (fun _ v -> Format.eprintf "%s" (contract_to_string v)) ct; *)
  (* typecheck_contract gamma ((Hashtbl.find ct cname)) ct; *)

  if fname = "bank_example" then 
    (
      let (ct, blockchain, _, sigma, vars) = parse_file "contracts/bank.sol" ct blockchain blockchain sigma vars in
      Hashtbl.iter (fun _ c -> typecheck_contract gamma c ct) ct;
      bank_example ct vars blockchain sigma;
      print_blockchain blockchain vars
    )
  else if fname = "wallet_example" then  
    (
      let (ct, blockchain, _, sigma, vars) = parse_file "contracts/wallet.sol" ct blockchain blockchain sigma vars in
      Hashtbl.iter (fun _ c -> typecheck_contract gamma c ct) ct;
      wallet_example ct vars blockchain sigma;
      print_blockchain blockchain vars)
  else if fname = "inheritance_example"  then  
    (
      let (ct, blockchain, _, sigma, vars) = parse_file "contracts/inheritance.sol" ct blockchain blockchain sigma vars in
      Hashtbl.iter (fun _ c -> typecheck_contract gamma c ct) ct;
      inheritance_example ct vars blockchain sigma;
      print_blockchain blockchain vars)
  else
    let (ct, _blockchain, _, _sigma, _vars) = parse_file fname ct blockchain blockchain sigma vars in
    Hashtbl.iter (fun _ c -> typecheck_contract gamma c ct) ct
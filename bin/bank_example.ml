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

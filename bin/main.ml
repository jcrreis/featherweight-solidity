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

let test_linearization_py ct b = 
  if b then 
    (Hashtbl.add ct "D" {name="D"; super_contracts=["B"; "C"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    Hashtbl.add ct "C" {name="C"; super_contracts=["A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    Hashtbl.add ct "B" {name="B"; super_contracts=["A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    Hashtbl.add ct "A" {name="A"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    c3_linearization "D" ct)
  else 
    (Hashtbl.add ct "D" {name="D"; super_contracts=["B"; "C"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    Hashtbl.add ct "C" {name="C"; super_contracts=["A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    Hashtbl.add ct "B" {name="B"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    Hashtbl.add ct "A" {name="A"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
    c3_linearization "D" ct)

let test_linearization_succ ct = 
  Hashtbl.add ct "D" {name="D"; super_contracts=["B"; "C"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "C" {name="C"; super_contracts=["A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "B" {name="B"; super_contracts=["A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "A" {name="A"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "E" {name="E"; super_contracts=["D"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  c3_linearization "E" ct

let test_linearization_fail ct = 
  Hashtbl.add ct "A" {name="A"; super_contracts=[]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "B" {name="B"; super_contracts=["A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "C" {name="C"; super_contracts=["B"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "D" {name="D"; super_contracts=["C"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "E" {name="E"; super_contracts=["D";"A"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "F" {name="E"; super_contracts=["E"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};
  Hashtbl.add ct "G" {name="E"; super_contracts=["A";"F"]; super_constructors_args=[]; state=[]; constructor=([], Val(VUnit)); functions=[]};

  c3_linearization "G" ct

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
  (* let rec show_hierarchy = function
    | Class (n, _) -> n
      and show_hierarchy_list lat =
      "[" ^ String.concat ", " (List.map show_hierarchy lat) ^ "]"
      and c = Class ("C", [])
      and a = Class ("A", [c])
      and b = Class ("B", [c])
      and eoac = Class ("EOAContract", [b;a])
      (* and a = Class ("A", [o])
      and b = Class ("B", [o])
      and c = Class ("C", [o])
      and d = Class ("D", [o])
      and e = Class ("E", [o])
      and k1 = Class ("K1", [a; b; c])
      and k2 = Class ("K2", [d; b; e])
      and k3 = Class ("K3", [d; a])
      and z = Class ("Z", [k1; k2; k3])
      and o = Class ("O", []) *)
   in
   print_endline @@ show_hierarchy eoac;
   match c3 eoac with
    | Some v -> print_endline @@ show_hierarchy_list v
    | None -> print_endline "No linearization"; *)
    (* let test_contract_hierarchy ct b = 
      Hashtbl.add ct "B" (b_contract());
      Hashtbl.add ct "A" (a_contract());
      Hashtbl.add ct "EOAContract" (eoa_contract());
      if b then 
        Hashtbl.add ct "C" (c_contract())
      else
        Hashtbl.add ct "C" (eoa_contract());
      let lst = get_contract_hierarchy (eoa_contract()) ct in 
      Format.eprintf "["; 
      List.iteri (fun i x -> 
        if i <> ((List.length lst) - 1) then Format.eprintf "%s;" x
        else Format.eprintf "%s" x
        ) lst;
      Format.eprintf "]\n"; 
    in   *)
    (* test_contract_hierarchy ct true; *)
    
    let lst = test_linearization_py ct false in 
    Format.eprintf "[";
    List.iteri (fun i x -> 
      if i <> ((List.length lst) - 1) then Format.eprintf "%s;" x
      else Format.eprintf "%s" x
      ) lst;
      Format.eprintf "]\n"; 
    let lst = test_linearization_succ ct in 
      Format.eprintf "[";
      List.iteri (fun i x -> 
        if i <> ((List.length lst) - 1) then Format.eprintf "%s;" x
        else Format.eprintf "%s" x
        ) lst;
      Format.eprintf "]\n"; 
      try 
        let lst = test_linearization_fail ct in 
        Format.eprintf "[";
        List.iteri (fun i x -> 
          if i <> ((List.length lst) - 1) then Format.eprintf "%s;" x
          else Format.eprintf "%s" x
          ) lst;
          Format.eprintf "]\n";
      with No_linearization -> Format.eprintf "Cannot create a consistent method resolution order\n";
    Format.eprintf "%s" "===================================\n";
    Format.eprintf "%s\n\n" (contract_to_string (b_contract()));
    Format.eprintf "%s\n\n" (contract_to_string (c_contract()));
    let test_contract_builder ct = 
      let a_with_super = contract_with_super_contracts (a_contract()) ct in 
      match a_with_super with
      | Ok (c, contract_table) -> 
        begin 
          Format.eprintf "%s\n\n" (contract_to_string c);
          let b_with_super = contract_with_super_contracts (b_contract()) contract_table in 
          match b_with_super with 
            | Ok (_c, contract_table) -> 
              begin 
                let eoac_with_super = contract_with_super_contracts (eoa_contract()) contract_table in 
                match eoac_with_super with
                  | Ok (c, _ct) -> Format.eprintf "%s\n\n" (contract_to_string c);
                  | Error s -> Format.eprintf "%s\n\n" s;
              end
            | Error s -> Format.eprintf "%s\n\n" s;
        end 
      | Error s -> Format.eprintf "%s\n\n" s;
    in

    test_contract_builder ct;
    let e = New("EOAContract", Val(VUInt 10000), [Val(VUInt 8765321)]) in 
    Format.eprintf "\n%s\n" (expr_to_string e);
    let conf = (blockchain, blockchain, sigma, e) in 
    let (blockchain, _blockchain', _sigma, res) = eval_expr ct vars conf in
    match res with 
      | Revert -> Format.eprintf "Revert@.";
      | _ -> Format.eprintf "Result: %s@." (expr_to_string res);
    Format.eprintf "Blockchain: @.";
    print_blockchain blockchain vars;
    


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
    typecheck (Hashtbl.create 64) (MsgSender) (UInt) ct blockchain;
    
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

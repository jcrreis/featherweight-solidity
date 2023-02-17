open Featherweightsolidity  
open Fs 
open Types
open Pprinters


let fname = Sys.argv.(1)

let print_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Format.eprintf "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


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
    (* Hashtbl.add ct "Bank" (bank_contract());
    Hashtbl.add ct "BloodBank" (blood_bank_contract());
    Hashtbl.add ct "Donor" (donor_contract());
    Hashtbl.add ct "EOAContract" (eoa_contract()); *)
    let (_, _, _, e1) = eval_expr ct vars (blockchain, blockchain, sigma, AritOp(Minus(Val(VUInt 2), Val(VUInt 3)))) in
    Format.eprintf "\n RESULTADO:  %s" (expr_to_string e1 vars); 
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

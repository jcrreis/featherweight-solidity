(* BEFORE 0.5.0 there was no distinction between address and address payable!!!
 * *)
(* msg.sender.transfer(x) to payable(msg.sender).transfer(x) *)

open Cryptokit
open Types
(* open Pprinters  *)

let eval_arit_expr (e: arit_ops) : expr = match e with
  | Plus (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt(n1 + n2))
      | _ -> assert false
    end
  | Div (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> 
        if n2 = 0 then 
          Revert
        else
          Val (VUInt (n1 / n2))
      | _ -> assert false
    end
  | Times (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt (n1 * n2))
      | _ -> assert false
    end
  | Minus (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt (n1 - n2))
      | _ -> assert false
    end
  | Exp (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt ((float_of_int n1) ** (float_of_int n2) |> int_of_float))
      | _ -> assert false
    end
  | Mod (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> 
        if n2 = 0 then
          Revert
        else 
          Val (VUInt (n1 mod n2))
      | _ -> assert false
    end

let eval_bool_expr (e: bool_ops) : expr = match e with
  | Neg b1 -> begin match b1 with
      | Val (VBool (True)) -> Val (VBool (False))
      | Val (VBool (False)) -> Val (VBool (True))
      | _ -> assert false
    end
  | Conj (e1, e2) -> begin match e1, e2 with
      | Val (VBool (True)), Val (VBool (True)) -> Val (VBool (True))
      | Val (VBool (True)),  Val (VBool (False)) -> Val (VBool (False))
      | Val (VBool (False)), Val (VBool (True)) -> Val (VBool (False))
      | Val (VBool (False)), Val (VBool (False)) -> Val (VBool (False))
      | _ -> assert false
    end
  | Disj (e1, e2) -> begin match e1, e2 with
      | Val (VBool (True)), Val (VBool (True)) -> Val (VBool (True))
      | Val (VBool (True)),  Val (VBool (False)) -> Val (VBool (True))
      | Val (VBool (False)), Val (VBool (True)) -> Val (VBool (True))
      | Val (VBool (False)), Val (VBool (False)) -> Val (VBool (False))
      | _ -> assert false
    end
  | Equals (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> if n1 = n2 then Val (VBool (True)) else Val (VBool (False))
      | _ -> assert false
    end
  | Greater (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> if n1 > n2 then Val (VBool (True)) else Val (VBool (False))
      | _ -> assert false
    end
  | GreaterOrEquals (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> if n1 >= n2 then Val (VBool (True)) else Val (VBool (False))
      | _ -> assert false
    end
  | Lesser (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> if n1 < n2 then Val (VBool (True)) else Val (VBool (False))
      | _ -> assert false
    end
  | LesserOrEquals (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> if n1 <= n2 then Val (VBool (True)) else Val (VBool (False))
      | _ -> assert false
    end
  | Inequals (e1, e2) -> begin match e1, e2 with
      | Val (VUInt n1), Val (VUInt n2) -> if n1 != n2 then Val (VBool (True)) else Val (VBool (False))
      | _ -> assert false
    end


let generate_new_ethereum_address () : string =
  (* https://ethereum.stackexchange.com/questions/3542/how-are-ethereum-addresses-generated*)
  let rsa_key = RSA.new_key 512 in
  let rsa_public_key = rsa_key.e in
  let keccak_key = hash_string (Hash.keccak 256) rsa_public_key in
  let address = transform_string (Hexa.encode()) keccak_key in
  "0x" ^ (String.sub address 24 40)



let state_vars_contract (contract_name: string) (ct: (string, contract_def) Hashtbl.t) : (t_exp * string) list =
  let contract : contract_def = Hashtbl.find ct contract_name in contract.state


let function_body
    (contract_name: string)
    (function_name: string)
    (values: expr list)
    (ct: (string, contract_def) Hashtbl.t) :
  ((t_exp * string) list) * expr =
  let contract : contract_def = Hashtbl.find ct contract_name in
  let functions_def : fun_def list = contract.functions in
  try
    let f = List.find (fun (x : fun_def) -> x.name = function_name) (functions_def) in
    if List.length values = List.length f.args then (f.args, f.body) else ([], Return Revert)
  with Not_found -> ([], Return Revert)


let top
    (conf: conf) : values =
  let (_, _, sigma, _) = conf in
  try
    Stack.top sigma
  with Stack.Empty -> VUnit


let rec eval_expr
    (ct: (string, contract_def) Hashtbl.t)
    (vars: (string, expr) Hashtbl.t)
    (conf: conf) : conf
  =
  let (blockchain, blockchain', sigma, e) = conf in
  let get_contract_by_address (blockchain: blockchain ) (address: values) : values =
    Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k2 = address then k1 else acc) blockchain VUnit
  in
  let get_address_by_contract (blockchain: blockchain ) (contract: values) : values =
    Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k1 = contract then k2 else acc) blockchain VUnit
  in
  (*uptbal(β, a, n)*)
  let update_balance
      (ct: (string, contract_def) Hashtbl.t)
      (address: values)
      (value: values)
      (vars: (string, expr) Hashtbl.t)
      (conf: conf) : (blockchain, unit) result =
    let (blockchain, blockchain', sigma, _) = conf in
    let get_contract_by_address (blockchain: ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t ) (address: values) =
      Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k2 = address then k1 else acc) blockchain VUnit
    in
    let contract = get_contract_by_address blockchain address in
    let (c, sv, old_balance) = Hashtbl.find blockchain (contract, address) in
    match eval_expr ct vars (blockchain, blockchain', sigma, (AritOp (Plus (Val old_balance, Val value)))) with
    | (_, _, _, Val new_balance) ->
      begin match new_balance with
        | VUInt i -> if i < 0 then Error () else (Hashtbl.replace blockchain (contract, address) (c, sv, new_balance) ; Ok blockchain)
        | _ -> assert false
      end
    | _ -> assert false
  in
  let get_default_for_type (t_e: t_exp) : (expr) = match t_e with 
    | C _ -> Val(VContract(0))
    | Bool -> Val(VBool(False))
    | UInt -> Val(VUInt(0))
    | Address -> Val(VAddress("0x0000000000000000000000000000000000000000"))
    | Map (_t1, t2) -> Val(VMapping(Hashtbl.create 64, t2))
    | Fun (_t1, _t2) -> Revert
    | Unit -> assert false
    | TRevert -> assert false
  in
  let init_contract_state (state: (t_exp * string) list) : (expr) StateVars.t =
    List.fold_left (fun sv (t_e, s) -> 
                    match t_e with
                      | C (_n) -> StateVars.add s (Val(VContract(0))) sv
                      | Bool -> StateVars.add s (Val(VBool(False))) sv
                      | UInt -> StateVars.add s (Val(VUInt(0))) sv
                      | Address -> StateVars.add s (Val(VAddress("0x0000000000000000000000000000000000000000"))) sv
                      | Map (_t1, t2) -> StateVars.add s (Val(VMapping(Hashtbl.create 64, t2))) sv
                      | Fun (_t1, _t2) -> StateVars.add s Revert sv
                      | Unit -> assert false
                      | TRevert -> assert false
                  ) StateVars.empty state
  in
  match e with
  | AritOp a1 -> begin match a1 with
      | Plus (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then
              (blockchain, blockchain', sigma, Revert)
            else  
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Plus (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert)
            else
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Plus (e1', e2)))
        end
      | Div (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
          | e1, Val (VUInt i) -> 
            if i = 0 
            then 
              (blockchain, blockchain', sigma, Revert) 
            else 
            begin  
              let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
              if e1' = Revert then 
                (blockchain, blockchain', sigma, Revert) 
              else  
                eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Div (e1', Val (VUInt i))))
            end
          | e1, e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Div (e1, e2')))
        end
      | Times (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else  
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Times (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Times (e1', e2)))
        end
      | Minus (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Minus (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Minus (e1', e2)))
        end
      | Exp (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else    
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Exp (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Exp (e1', e2)))
        end
      | Mod (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
          | e1, Val (VUInt i) -> 
            if i = 0 
            then 
              (blockchain, blockchain', sigma, Revert) 
            else 
            begin  
              let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
              if e1' = Revert then 
                (blockchain, blockchain', sigma, Revert) 
              else    
                eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Mod (e1', Val (VUInt i))))
            end
          | e1, e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Mod (e1, e2')))
        end
    end
  | BoolOp b1 -> begin match b1 with
      | Neg e1 -> begin match e1 with
          | Val (VBool(_)) -> (blockchain, blockchain', sigma, eval_bool_expr b1)
          | _ -> 
            if e1 = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else
              let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in  
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Neg e1'))
        end
      | Conj (e1, e2) -> begin match e1, e2 with
          | Val (VBool(_)), Val (VBool(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VBool b), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Conj (Val (VBool b), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Conj (e1', e2)))
        end
      | Disj (e1, e2) -> begin match e1, e2 with
          | Val (VBool(_)), Val (VBool(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VBool b), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Disj (Val (VBool b), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Disj (e1', e2)))
        end
      | Equals (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Equals (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Equals (e1', e2)))
        end
      | Greater (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Greater (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Greater (e1', e2)))
        end
      | GreaterOrEquals (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(GreaterOrEquals (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(GreaterOrEquals (e1', e2)))
        end
      | Lesser (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Lesser (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Lesser (e1', e2)))
        end
      | LesserOrEquals (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(LesserOrEquals (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(LesserOrEquals (e1', e2)))
        end
      | Inequals (e1, e2) -> begin match e1, e2 with
          | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
          | Val (VUInt i), e2 -> 
            let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
            if e2' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Inequals (Val (VUInt i), e2')))
          | e1, e2 -> 
            let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
            if e1' = Revert then 
              (blockchain, blockchain', sigma, Revert) 
            else 
              eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Inequals (e1', e2)))
        end
    end
  | Var(x) ->
          begin try
            (blockchain, blockchain', sigma, Hashtbl.find vars x)
          with Not_found -> Printf.printf  "Couldnt find Var: %s\n" x; (blockchain, blockchain', sigma, Revert)
          end
  | Val e1 -> (blockchain, blockchain', sigma, Val e1)
  | This None -> (blockchain, blockchain', sigma, Hashtbl.find vars "this")
  | This (Some s) -> let (_, _, _, this) = eval_expr ct vars (blockchain, blockchain', sigma, This None) in
    begin match this with
      | Val(VContract c) -> let a = get_address_by_contract blockchain (VContract c) in
        let (cname, _, _) = Hashtbl.find blockchain (VContract c, a) in
        let (_t_es, body) = function_body cname s [] ct in  (* [] -> function args, what to pass?*)
        (blockchain, blockchain', sigma, body)
      | _ -> (blockchain, blockchain', sigma, Revert)
    end
  | MsgSender -> (blockchain, blockchain', sigma, Hashtbl.find vars "msg.sender")
  | MsgValue -> (blockchain, blockchain', sigma, Hashtbl.find vars "msg.value")
  | Balance e1 -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VAddress a)) ->
        let c =  get_contract_by_address blockchain (VAddress a) in
        let (_, _, v) = Hashtbl.find blockchain (c, VAddress a) in
        (blockchain, blockchain', sigma, Val(v))
      | _ -> (blockchain, blockchain', sigma, Revert)
    end
  | Address e1 ->  begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VContract c)) ->
        let a =  get_address_by_contract blockchain (VContract c) in 
        (blockchain, blockchain', sigma, Val a)
      | _ -> assert false
    end
  | StateRead (e1, s) ->  begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VContract c)) ->
        let a = get_address_by_contract blockchain (VContract c) in
        let (_, sv, _) = Hashtbl.find blockchain (VContract c,a) in
        begin try 
          let res = StateVars.find s sv in
          eval_expr ct vars (blockchain, blockchain', sigma, res) 
        with Not_found -> Format.eprintf "State var : %s NOT FOUND" s; (blockchain, blockchain', sigma, Revert)
        end
      | _ -> assert false
    end
  (*VER*)
  | Transfer (e1, e2) -> 
    if (top conf) = VUnit 
      then (blockchain, blockchain', sigma, Revert)
    else 
      begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
        | (_, _, _, Val(VAddress a)) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e2) with
            | (_, _, _, Val(VUInt v)) ->
              let res = update_balance ct (VAddress a) (VUInt (-v)) vars conf in
              begin match res with
                | Ok blockchain ->
                  let res = update_balance ct (VAddress a) (VUInt (-v)) vars conf in
                  begin match res with 
                    | Ok blockchain -> 
                      let ctr: values = get_contract_by_address blockchain (VAddress a) in 
                      let (cname, _, _) = Hashtbl.find blockchain (ctr, VAddress a) in 
                      Hashtbl.add vars "msg.sender" (Val(top conf));
                      Hashtbl.add vars "msg.value" (Val(VUInt v));
                      Hashtbl.add vars "this" (Val ctr);
                      Stack.push (VAddress a) sigma;
                      let (_, e) = function_body cname "fb" [] ct in 
                      (blockchain, blockchain', sigma, e)
                    | Error () -> (blockchain, blockchain', sigma, Revert)
                  end
                | Error () -> (blockchain, blockchain', sigma, Revert)
              end
            | _ -> assert false
          end
        | _ -> assert false
      end
  (*VER*)
  | New (s, e1, le) ->
    begin
      let c = Hashtbl.length blockchain in
      let a = generate_new_ethereum_address() in
      let contract_def: contract_def = Hashtbl.find ct s in
      let (t_es, body) = contract_def.constructor in
      if (List.length t_es = List.length le) && ((top conf) != VUnit) then
        begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
          | (_, _, _, Val (VUInt n)) ->
            let res = update_balance ct (top conf) (VUInt (-n)) vars conf in
            begin match res with
              | Ok blockchain ->
                let sv = init_contract_state contract_def.state in
                Hashtbl.add blockchain (VContract c, VAddress a) (contract_def.name, sv, VUInt(n));
                Hashtbl.add vars "this" (Val(VContract c));
                List.iter2 (fun (_, s) e -> let (_, _, _, e') = eval_expr ct vars (blockchain, blockchain', sigma, e) in 
                Hashtbl.add vars s e') t_es le;
                let (blockchain, blockchain', sigma, _) = eval_expr ct vars (blockchain, blockchain', sigma, body) in
                List.iter (fun (_, s) -> Hashtbl.remove vars s) t_es;
                (blockchain, blockchain', sigma, Val(VContract c))
              | Error () -> (blockchain, blockchain', sigma, Revert)
            end
          | _ -> (blockchain, blockchain', sigma, Revert)
        end
      else if (List.length t_es = List.length le) && ((top conf) == VUnit) then
        begin
          match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
          | (_, _, _, Val (VUInt n)) ->
              let sv = init_contract_state contract_def.state in
              Hashtbl.add blockchain (VContract c, VAddress a) (contract_def.name, sv, VUInt(n));
              Hashtbl.add vars "this" (Val(VContract c));
              List.iter2 (fun (_, s) e -> let (_, _, _, e') = eval_expr ct vars (blockchain, blockchain', sigma, e) in 
                  Hashtbl.add vars s e') t_es le;
              let (blockchain, blockchain', sigma, _) = eval_expr ct vars (blockchain, blockchain', sigma, body) in
              List.iter (fun (_, s) -> Hashtbl.remove vars s) t_es;
              (blockchain, blockchain', sigma, Val(VContract c))
          | _ -> (blockchain, blockchain', sigma, Revert)
        end
      else
        (blockchain, blockchain', sigma, Revert)
    end
  | Cons (s, e1) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with (*Contract_Name(address) C(e)*)  (*CAST*)
      | (_, _, _, Val(VAddress a)) ->
        let c = get_contract_by_address blockchain (VAddress a) in
        let (cname, _, _) = Hashtbl.find blockchain (c, VAddress a) in
        if cname = s then
          (blockchain, blockchain', sigma, Val c)
        else
          (blockchain, blockchain', sigma, Revert)
      | _ -> assert false
    end
  | Seq (e1, e2) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Revert) -> eval_expr ct vars (blockchain, blockchain', sigma, Revert)
      | _ -> begin match top conf with
          | VUnit -> eval_expr ct vars (blockchain, blockchain, sigma, e2) (* empty call stack *) (*commit blockchain changes*)
          | _ -> eval_expr ct vars (blockchain, blockchain', sigma, e2)
        end
    end
  | Let (_, x, e1, e2) ->
    begin if Hashtbl.mem vars x  (* verify if x está em vars, modificação à tese do pirro*)
      then 
        (blockchain, blockchain', sigma, Revert) 
      else 
      let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
        Hashtbl.add vars x e1'; eval_expr ct vars (blockchain, blockchain', sigma, e2)
    end
  | Assign (x, e1) ->
    let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
    Hashtbl.replace vars x e1';
    eval_expr ct vars (blockchain, blockchain', sigma, Val VUnit)
  | If (e1, e2, e3) -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
    begin match e1' with
      | Val (VBool b) -> begin match b with
          | True -> eval_expr ct vars (blockchain, blockchain', sigma, e2) 
          | False -> eval_expr ct vars (blockchain, blockchain', sigma, e3)
        end
      | _ -> assert false
    end
  | Call (e1, s, e2, le) ->
    begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VContract c)) ->
        let a = get_address_by_contract blockchain (VContract c) in
        begin match eval_expr ct vars (blockchain, blockchain', sigma, e2) with
          | (_, _, _, Val(VUInt n)) ->
            let res = update_balance ct (top conf) (VUInt (-n)) vars conf in
            begin match res with
              | Ok blockchain ->
                let (contract_name, _, _) = Hashtbl.find blockchain (VContract c, a) in
                let (args, body) = function_body contract_name s le ct in
                if body = Return Revert then
                  (blockchain, blockchain', sigma, Revert)
                else
                  begin
                    Hashtbl.add vars "msg.sender" (Val(top conf));
                    Hashtbl.add vars "msg.value" (Val(VUInt n));
                    Hashtbl.add vars "this" (Val(VContract c));
                    Stack.push (top conf) sigma;
                    begin   
                      try
                        List.iter2 (fun arg value -> if Hashtbl.mem vars arg then () else Hashtbl.add vars arg value) (List.map (fun (_, v) -> v) args) le;
                        let (blockchain, blockchain', sigma, es) = eval_expr ct vars (blockchain, blockchain', sigma, body) in
                        List.iter (fun arg -> Hashtbl.remove vars arg) (List.map (fun (_, v) -> v) args);
                        Hashtbl.remove vars "this";
                        Hashtbl.remove vars "msg.sender";
                        Hashtbl.remove vars "msg.value";
                        eval_expr ct vars (blockchain, blockchain', sigma, es)
                      with Invalid_argument _ -> (blockchain, blockchain', sigma, Revert)
                    end
                  end
              | Error () -> (blockchain, blockchain', sigma, Revert)
            end
          | _ -> assert false
        end
      | _ -> assert false
    end 
  | CallTopLevel (e1, s, e2, e3, le) ->
    begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
    | (_, _, _, Val(VContract c)) ->
      let a = get_address_by_contract blockchain (VContract c) in
      begin match eval_expr ct vars (blockchain, blockchain', sigma, e2) with
        | (_, _, _, Val(VUInt n)) ->
          let res = begin match eval_expr ct vars (blockchain, blockchain', sigma, e3) with
            | (_, _, _, Val(a')) -> update_balance ct a' (VUInt (-n)) vars conf
            | _ -> assert false
          end in
          begin match res with
            | Ok blockchain ->
              let (contract_name, _, _) = Hashtbl.find blockchain (VContract c, a) in
              let (args, body) = function_body contract_name s le ct in
              if body = Return Revert then
                (blockchain, blockchain', sigma, Revert)
              else
                begin
                  let (_, _, _, e3') = eval_expr ct vars (blockchain, blockchain', sigma, e3) in
                  Hashtbl.add vars "msg.sender" e3';
                  Hashtbl.add vars "msg.value" (Val(VUInt n));
                  Hashtbl.add vars "this" (Val(VContract c));
                  Stack.push a sigma;
                  begin
                    try
                      List.iter2 (fun arg value -> Hashtbl.add vars arg value) (List.map (fun (_, v) -> v) args) le;
                      let (blockchain, blockchain', sigma, es) = eval_expr ct vars (blockchain, blockchain', sigma, body) in
                      List.iter (fun arg -> Hashtbl.remove vars arg) (List.map (fun (_, v) -> v) args);
                      Hashtbl.remove vars "this";
                      Hashtbl.remove vars "msg.sender";
                      Hashtbl.remove vars "msg.value";
                      eval_expr ct vars (blockchain, blockchain', sigma, es)
                    with Invalid_argument _ -> (blockchain, blockchain', sigma, Revert)
                  end
                end
            | Error () -> (blockchain, blockchain', sigma, Revert)
          end
        | _ -> assert false
      end
    | _ -> assert false
  end
  | Revert ->
    if top conf != VUnit then
      let _ = Stack.pop sigma in
      (blockchain, blockchain', sigma, Revert)
    else
      (blockchain, blockchain', sigma, Revert)
  | StateAssign (e1, s , e2) ->
    begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VContract c)) ->
        let a = get_address_by_contract blockchain (VContract c) in
        let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
        let (c_name, map, n) = Hashtbl.find blockchain (VContract c, a) in
        let map' = StateVars.add s e2' map in
        Hashtbl.replace blockchain (VContract(c),a) (c_name, map', n);
        (blockchain, blockchain', sigma, e2')
      | _ -> assert false
    end
  | MapRead (e1, e2) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VMapping(m, t_e))) ->
        let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
        begin try
          let res = Hashtbl.find m e2' in 
          (blockchain, blockchain', sigma, res)
        with Not_found -> (blockchain, blockchain', sigma, (get_default_for_type t_e))
        end
      | _ -> assert false
    end
  | MapWrite (e1, e2, e3) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VMapping (m, t_e))) ->
        let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
        let (_, _, _, e3') = eval_expr ct vars (blockchain, blockchain', sigma, e3) in
        Hashtbl.add m e2' e3' ; (blockchain, blockchain', sigma, Val(VMapping (m, t_e)))
      | _ -> assert false
    end
  | Return e1 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
    if top conf != VUnit then
      let _ = Stack.pop sigma in
      (blockchain, blockchain', sigma, e1')
    else
      (blockchain, blockchain', sigma, e1')
  | AddContract cdef -> 
    begin 
      let fun_names = (List.map (fun (f_def: fun_def) -> f_def.name) cdef.functions) in
      if List.mem "fb" fun_names || List.mem "receive" fun_names
      then 
      begin
        Hashtbl.add ct cdef.name cdef; (blockchain, blockchain', sigma, Val(VUnit))
      end
      else 
        (blockchain, blockchain', sigma, Revert)
    end
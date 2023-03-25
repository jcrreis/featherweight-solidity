open Types
open Cryptokit
(* open Pprinters  *)
open C3


module FV = Set.Make(String)
module FN = Set.Make(String)
module SS = Set.Make(String)

let rec free_variables (e: expr) : FV.t =
  let rec union_list_set (lst: FV.t list) (set: FV.t): FV.t = match lst with
    | [] -> set
    | x :: xs -> union_list_set xs (FV.union set x)
  in
  match e with 
  | AritOp a1 -> begin match a1 with
      | Plus (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Div (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Times (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Minus (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Exp (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Mod (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    end
  | BoolOp b1 -> begin match b1 with
      | Neg e1 -> free_variables e1
      | Conj (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Disj (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Equals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Greater (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | GreaterOrEquals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Lesser (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | LesserOrEquals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
      | Inequals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    end
  | Val _ -> FV.empty
  | Var x -> FV.singleton x
  | This _s -> FV.singleton "this"
  | MsgSender -> FV.singleton "msg.sender"
  | MsgValue -> FV.singleton "msg.value"
  | Balance e1 -> free_variables e1
  | Address e1 -> free_variables e1
  | StateRead (e1, _) ->  free_variables e1
  | Transfer (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | New (_, e1, le) -> let set_list = List.map free_variables le in
    FV.union (free_variables e1) (union_list_set set_list FV.empty)
  | Cons (_, e1) -> free_variables e1
  | Seq (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | Let(_, x, e1, e2) -> FV.union (free_variables e1) ((FV.filter (fun (x') -> x <> x') (free_variables e2)))
  | Assign (x, e1) -> FV.union (FV.singleton x) (free_variables e1)
  | If (e1, e2, e3) -> FV.union (free_variables e1) (FV.union (free_variables e2) (free_variables e3))
  | Call (e1, _, e2, _le) -> FV.union (free_variables e1) (free_variables e2)
  | CallTopLevel (e1, _, e2, e3, _le) -> FV.union (free_variables e1) (FV.union (free_variables e2) (free_variables e3))
  | Revert -> FV.empty
  | StateAssign (e1, _ , e2) -> FV.union (free_variables e1) (free_variables e2)
  | MapRead (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | MapWrite (e1, e2, e3) -> FV.union (free_variables e1) (FV.union (free_variables e2) (free_variables e3))
  | Return e1 -> free_variables e1
  | _ -> assert false


let rec free_addr_names (e: expr) : FN.t =
  let rec union_list_set (lst: FN.t list) (set: FN.t): FN.t = match lst with
    | [] -> set
    | x :: xs -> union_list_set xs (FN.union set x)
  in
  match e with
  | AritOp a1 -> begin match a1 with
      | Plus (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Div (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Times (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Minus (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Exp (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Mod (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    end
  | BoolOp b1 -> begin match b1 with
      | Neg e1 -> free_variables e1
      | Conj (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Disj (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Equals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Greater (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | GreaterOrEquals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Lesser (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | LesserOrEquals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
      | Inequals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    end
  | Val (VAddress a) -> FN.singleton a
  | Val (VContract _c) -> FN.empty
  | Val _ -> FN.empty
  | This _s -> FN.empty
  | Var _x -> FN.empty
  | MsgSender -> FN.empty
  | MsgValue -> FN.empty
  | Address e1 -> free_addr_names e1
  | Balance e1 -> free_addr_names e1
  | StateRead (e1, _) -> free_addr_names e1
  | Transfer (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | New (_, e1, le) -> let set_list = List.map free_addr_names le in
    FN.union (free_addr_names e1) (union_list_set set_list FV.empty)
  | Cons (_, e1) -> free_addr_names e1
  | Seq (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | Let(_, _, e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | Assign (_, e1) -> free_variables e1
  | If (e1, e2, e3) -> FN.union (free_addr_names e1) (FV.union (free_addr_names e2) (free_addr_names e3))
  | Call (e1, _, e2, _le) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | CallTopLevel (e1, _, e2, e3, _le) ->  FN.union (free_addr_names e1) (FV.union (free_addr_names e2) (free_addr_names e3))
  | Revert -> FN.empty
  | StateAssign (e1, _ , e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | MapRead (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | MapWrite (e1, e2, e3) -> FN.union (free_addr_names e1) (FV.union (free_addr_names e2) (free_addr_names e3))
  | Return e1 -> free_addr_names e1
  | _ -> assert false


let rec substitute (e: expr) (e': expr) (x: string) : expr =
  let f lst = substitute lst e' x in
  match e with
  | AritOp a1 -> begin match a1 with
      | Plus (e1, e2) -> AritOp (Plus (substitute e1 e' x, substitute e2 e' x))
      | Div (e1, e2) ->  AritOp (Div (substitute e1 e' x, substitute e2 e' x))
      | Times (e1, e2) -> AritOp (Times (substitute e1 e' x, substitute e2 e' x))
      | Minus (e1, e2) ->  AritOp (Minus (substitute e1 e' x, substitute e2 e' x))
      | Exp (e1, e2) ->  AritOp (Exp (substitute e1 e' x, substitute e2 e' x))
      | Mod (e1, e2) ->  AritOp (Mod (substitute e1 e' x, substitute e2 e' x))
    end
  | BoolOp b1 -> begin match b1 with
      | Neg e1 -> BoolOp (Neg (substitute e1 e' x))
      | Conj (e1, e2) -> BoolOp(Conj (substitute e1 e' x, substitute e2 e' x))
      | Disj (e1, e2) -> BoolOp(Disj (substitute e1 e' x, substitute e2 e' x))
      | Equals (e1, e2) -> BoolOp(Equals (substitute e1 e' x, substitute e2 e' x))
      | Greater (e1, e2) -> BoolOp(Greater (substitute e1 e' x, substitute e2 e' x))
      | GreaterOrEquals (e1, e2) -> BoolOp(GreaterOrEquals (substitute e1 e' x, substitute e2 e' x))
      | Lesser (e1, e2) -> BoolOp(Lesser (substitute e1 e' x, substitute e2 e' x))
      | LesserOrEquals (e1, e2) -> BoolOp(LesserOrEquals (substitute e1 e' x, substitute e2 e' x))
      | Inequals (e1, e2) -> BoolOp(Inequals (substitute e1 e' x, substitute e2 e' x))
    end
  | Var y -> if x = y then e' else e
  | Val _ -> e
  | This _s -> if x = "this" then e' else e
  | MsgSender -> e
  | MsgValue -> e
  | Balance e1 -> Balance (substitute e1 e' x)
  | Address e1 -> Address (substitute e1 e' x)
  | StateRead (e1, s) -> StateRead (substitute e1 e' x, s)
  | Transfer (e1, e2) -> Transfer (substitute e1 e' x, substitute e2 e' x)
  | New (s, e1, le) -> New (s, substitute e1 e' x, List.map f le)
  | Seq (e1, e2) -> Seq (substitute e1 e' x, substitute e2 e' x)
  | Let (t_e, s, e1, e2) -> Let (t_e, s, substitute e1 e' x, substitute e2 e' x)
  | Assign (y, e1) -> Assign (y, substitute e1 e' x)
  | MapRead (e1, e2) -> MapRead (substitute e1 e' x, substitute e2 e' x)
  | MapWrite (e1, e2, e3) -> MapWrite (substitute e1 e' x, substitute e2 e' x, substitute e3 e' x)
  | If (e1, e2, e3) -> If (substitute e1 e' x, substitute e2 e' x, substitute e3 e' x)
  | Call (e1, s, e2, le) -> Call (substitute e1 e' x, s, substitute e2 e' x, List.map f le)
  | CallTopLevel (e1, s, e2, e3, le) ->  CallTopLevel (substitute e1 e' x, s, substitute e2 e' x, substitute e3 e' x, List.map f le)
  | Cons (s, e1) -> Cons (s, substitute e1 e' x)
  | Revert -> e
  | Return e1 -> Return e1
  | _ -> assert false

(* Blockchain maps cases? *)

let read_whole_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let generate_new_ethereum_address () : string =
  (* https://ethereum.stackexchange.com/questions/3542/how-are-ethereum-addresses-generated*)
  let rsa_key = RSA.new_key 512 in
  let rsa_public_key = rsa_key.e in
  let keccak_key = hash_string (Hash.keccak 256) rsa_public_key in
  let address = transform_string (Hexa.encode()) keccak_key in
  "0x" ^ (String.sub address 24 40)

let function_type (contract_name: string) (function_name: string) (ct: contract_table) : (t_exp list * t_exp) =
  let hierarchy : string list = c3_linearization contract_name ct in 
  let rec find_function (contract_hierarchy : string list) (function_name: string) (ct: contract_table) : (t_exp list * t_exp) = 
    match contract_hierarchy with 
      | [] -> ([], TRevert)
      | x :: xs -> 
        let contract : contract_def = Hashtbl.find ct x in  
        let functions_def : fun_def list = contract.functions in
        try
          let f = List.find (fun (x : fun_def) -> x.name = function_name) (functions_def) in
          let t_es = List.map (fun (t_e, _) -> t_e) f.args in
          (t_es, f.rettype)
        with Not_found -> find_function xs function_name ct 
  in
  find_function hierarchy function_name ct  

let function_body
(contract_name: string)
(function_name: string)
(values: expr list)
(ct: contract_table) :
((t_exp * string) list) * expr =
  let hierarchy : string list = c3_linearization contract_name ct in
  let rec find_function 
  (contract_hierarchy : string list) 
  (function_name : string) 
  (values : expr list)
  (ct: contract_table) :
  ((t_exp * string) list) * expr = 
    match contract_hierarchy with 
      | [] -> ([], Return Revert)
      | x :: xs -> 
        let contract : contract_def = Hashtbl.find ct x in  
        let functions_def : fun_def list = contract.functions in
        try
          let f = List.find (fun (x : fun_def) -> x.name = function_name) (functions_def) in
          if List.length values = List.length f.args then (f.args, f.body) else ([], Return Revert)
        with Not_found -> find_function xs function_name values ct
  in
  find_function hierarchy function_name values ct 


let encode_contract (content: string) : string =
  let keccak_key = hash_string (Hash.keccak 256) content in
  let encoded_contract = transform_string (Hexa.encode()) keccak_key in
  encoded_contract


let get_contract_by_address (contracts: contracts ) (address: values) : values =
  Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k2 = address then k1 else acc) contracts VUnit

let get_address_by_contract (contracts: contracts ) (contract: values) : values =
  Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k1 = contract then k2 else acc) contracts VUnit


let get_contract_hierarchy (contract: contract_def) (ct: (string, contract_def) Hashtbl.t) : string list =
  let visited = SS.singleton (contract.name) in
  let rec get_all_super_contracts (cs: string list) (ct: (string, contract_def) Hashtbl.t) (visited: SS.t) : string list =
    match cs with
    | [] -> []
    | x :: xs ->
      let contract_def: contract_def = Hashtbl.find ct x in
      let super_contract_hierarchy: string list = contract_def.super_contracts in
      let visited = SS.union visited (SS.singleton x) in 
      let super_contract_hierarchy: string list = 
        (List.fold_left (fun lst ctr -> 
            if List.mem ctr cs then 
              if SS.mem ctr visited then 
                raise (Failure "Mutually recursive inheritance detected")
              else 
                lst 
            else (List.append lst [ctr])
          ) [] super_contract_hierarchy)  in 
      let xs = List.append xs super_contract_hierarchy in
      x :: (get_all_super_contracts xs ct visited)
  in
  get_all_super_contracts contract.super_contracts ct visited


let fsender (contract_name: string) (function_name: string) (ct: contract_table) : (string option) option = 
  let contract_def: contract_def = Hashtbl.find ct contract_name in  
  let functions_list: fun_def list = contract_def.functions in 
  let rec find_function_def (f_list: fun_def list) (function_name: string) : (string option) option =
    match f_list with 
    | [] -> None 
    | x :: xs -> 
      if x.name = function_name then 
        Some x.annotation 
      else 
        find_function_def xs function_name 
  in
  find_function_def functions_list function_name  


(* let contract_with_super_contracts (contract: contract_def) (ct: (string, contract_def) Hashtbl.t) : (contract_def * contract_table, string) result =
  let append_identifier_to_state (state: (t_exp * string) list) (id: (t_exp * string)) : ((t_exp * string) list, string) result = 
    let rec is_allowed_to_append (state: (t_exp * string) list) (id: (t_exp * string)) : bool =  
      match state with 
      | [] -> true 
      | x :: xs -> 
        if snd x = snd id then false else is_allowed_to_append xs id 
    in
    let can_append = is_allowed_to_append state id in  
    if can_append then Ok(state @ [id]) else Error("Identifier " ^ snd id ^ " already exists in contract " ^ contract.name)
  in 
  let rec append_super_state_to_contract (contract_state: (t_exp * string) list) (super_contract_state: (t_exp * string) list) : ((t_exp * string) list, string) result = 
    match super_contract_state with 
    | [] -> Ok(contract_state) 
    | x :: xs -> 
      let res = append_identifier_to_state contract_state x in 
      match res with 
      | Ok(new_state) -> append_super_state_to_contract new_state xs 
      | Error(e) -> Error(e)
  in
  let append_function_to_list (contract_functions: fun_def list) (f: fun_def) : (fun_def list, string) result = 
    let rec is_allowed_to_append (c_functions: fun_def list) (fdef: fun_def) : bool =  
      match c_functions with 
      | [] -> true 
      | x :: xs -> 
        if x.name = fdef.name && x.args = fdef.args then false else is_allowed_to_append xs fdef 
    in
    let can_append = is_allowed_to_append contract_functions f in  
    if can_append then Ok(contract_functions @ [f]) else Error("Function " ^ f.name ^ " already exists in contract " ^ contract.name)
  in 
  let rec append_super_functions_to_contract (contract_funs: fun_def list) (super_contract_funs: fun_def list) : (fun_def list, string) result  =
    match super_contract_funs with 
    | [] -> Ok(contract_funs) 
    | x :: xs -> 
      let res = append_function_to_list contract_funs x in 
      match res with 
      | Error(e) -> Error(e)
      | Ok(new_contract_funs) -> append_super_functions_to_contract new_contract_funs xs 
  in

  if List.length contract.super_contracts = 0 then 
    begin
      Hashtbl.add ct contract.name contract;
      Ok(contract, ct) 
    end
  else
    let contract = List.fold_left (fun (contract: contract_def) (super_contract_name: string) -> 
        let super_contract: contract_def = Hashtbl.find ct super_contract_name in
        let res = append_super_state_to_contract contract.state super_contract.state in
        let state = match res with 
          | Error(e) -> raise (Failure e)
          | Ok(s) -> s
        in
        let res = append_super_functions_to_contract contract.functions super_contract.functions in
        let functions = match res with 
          | Error(e) -> raise (Failure e)
          | Ok(f) -> f
        in 
        let super_contracts: string list = super_contract.super_contracts in  
        let super_constructors_args: expr list list = super_contract.super_constructors_args in
        let contract = {
          name = contract.name; 
          state = state; 
          super_contracts = contract.super_contracts @ super_contracts;
          super_constructors_args = contract.super_constructors_args @ super_constructors_args; 
          constructor = contract.constructor; 
          functions = functions
        }
        in 
        Hashtbl.add ct contract.name contract;
        contract
      ) contract contract.super_contracts in  
    Ok(contract, ct)
 *)

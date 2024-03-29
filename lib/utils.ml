open Types
open Cryptokit



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

let function_type (contract_name: string) (function_name: string) (ct: (string, contract_def) Hashtbl.t) : (t_exp list * t_exp) =
  let contract : contract_def = Hashtbl.find ct contract_name in
  let lookup_table = contract.function_lookup_table in 
  try
    let f : fun_def = Hashtbl.find lookup_table function_name in     
    let t_es = List.map (fun (t_e, _) -> t_e) f.args in
    (t_es, f.rettype)
  with Not_found -> raise (Failure (Printf.sprintf "Function %s not found" function_name))


let function_body
    (contract_name: string)
    (function_name: string)
    (values: expr list)
    (ct: contract_table) :
  ((t_exp * string) list) * expr =
  let contract_def: contract_def = Hashtbl.find ct contract_name in 
  let lookup_table = contract_def.function_lookup_table in 
  try
    let f : fun_def = Hashtbl.find lookup_table function_name in 
    if List.length values = List.length f.args 
    then (f.args, f.body) 
    else 
      ([], Return Revert)
  with Not_found -> raise (Failure (Printf.sprintf "Function %s not found" function_name))


let encode_contract (content: string) : string =
  let keccak_key = hash_string (Hash.keccak 256) content in
  let encoded_contract = transform_string (Hexa.encode()) keccak_key in
  encoded_contract


let get_contract_by_address (contracts: contracts ) (address: values) : values =
  Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k2 = address then k1 else acc) contracts VUnit

let get_address_by_contract (contracts: contracts ) (contract: values) : values =
  Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k1 = contract then k2 else acc) contracts VUnit

let state_vars_contract (contract_name: string) (ct: (string, contract_def) Hashtbl.t) : (t_exp * string) list =
  let contract : contract_def = Hashtbl.find ct contract_name in contract.state

let fsender (contract_name: string) (function_name: string) (ct: contract_table) : (t_exp, string) result = 
  let contract_def: contract_def = Hashtbl.find ct contract_name in 
  let lookup_table = contract_def.function_lookup_table in 
  try
    let f : fun_def = Hashtbl.find lookup_table function_name in 
    match f.annotation with 
    | None -> Ok(Address None)
    | Some c -> Ok(Address (Some (C c)))
  with Not_found -> Error("Function not found!")



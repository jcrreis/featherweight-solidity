open Types 
(* open C3  *)
(* open Utils *)
open Pprinters 


let axioms (gamma: gamma) (e: expr) : (t_exp, string) result = match e with 
  | Val (VBool _) -> Ok(Bool)  
  | Val (VUInt n) -> if n >= 0 then Ok(UInt) else Error("Invalid integer")
  | Revert -> Ok(TRevert)
  | Val (VUnit) -> Ok(Unit)
  | Val (VAddress a) -> 
    begin 
      try 
        (* gamma_vars * gamma_addresses * gamma_contracts *)
        let (_, gamma_addresses, _) = gamma in 
        let a = Hashtbl.find gamma_addresses (VAddress a) in 
        Ok(a)
        (* if subtyping a t ct then () else raise (TypeMismatch (a, t)) *)
      with Not_found -> raise (UnboundVariable a)
    end
  | Val (VContract i) ->
    begin 
      try 
        let (_, _, gamma_contracts) = gamma in 
        let c = Hashtbl.find gamma_contracts (VContract i) in 
        Ok(c)
        (* if subtyping c t ct then () else raise (TypeMismatch (c, t)) *)
      with Not_found -> raise (UnboundVariable "")
    end 
  | MsgSender -> 
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars "msg.sender" in
        Ok(t_x)
        (* if subtyping t_x t ct then () else raise (TypeMismatch (t_x, t)) *)
      with Not_found -> raise (UnboundVariable "msg.sender")
    end 
  | MsgValue -> Ok(UInt)
  | Var x -> 
    begin 
      try 
        Format.eprintf "\n%s" x;
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars x in
        Ok(t_x)
        (* Format.eprintf "%s ----> %s" (t_exp_to_string t_x) (t_exp_to_string t); *)
        (* if subtyping t_x t ct then () else raise (TypeMismatch (t_x, t)) *)
      with Not_found -> raise (UnboundVariable x)
    end 
  | _ -> assert false


let rec infer_type (gamma: gamma) (e: expr) (ct: contract_table) : (t_exp, string) result = 
  let type_infer_error t_exp : string = "Couldn't infer type " ^ (t_exp_to_string t_exp) in 
  let check_if_operands_uint (e1: expr) (e2: expr) (gamma: gamma) (ct: contract_table) : bool =
    let t_e1 = infer_type gamma e1 ct in 
    let t_e2 = infer_type gamma e2 ct in 
    match t_e1, t_e2 with 
      | Ok(t_e1), Ok(t_e2) -> if t_e1 = UInt && t_e2 = UInt then true else false 
      | _-> false 
  in 
  let check_if_operands_bool (e1: expr) (e2: expr) (gamma: gamma) (ct: contract_table) : bool =
    let t_e1 = infer_type gamma e1 ct in 
    let t_e2 = infer_type gamma e2 ct in 
    match t_e1, t_e2 with 
      | Ok(t_e1), Ok(t_e2) -> if t_e1 = Bool && t_e2 = Bool then true else false 
      | _-> false 
  in
  let infer_arit (gamma: gamma) (a: arit_ops) (ct: contract_table) : (t_exp, string) result = match a with 
    | Plus (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Div (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Times (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Minus (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Exp (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Mod (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
  in
  let infer_bool (gamma: gamma) (b: bool_ops) (ct: contract_table) : (t_exp, string) result = match b with 
    | Neg e1 -> 
      let t_e1 = infer_type gamma e1 ct in 
      t_e1
    | Conj (e1, e2) -> 
      if check_if_operands_bool e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Disj (e1, e2) ->
      if check_if_operands_bool e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Equals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)

      (* if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      begin 
        try 
          typecheck gamma e1 UInt ct blockchain;
          typecheck gamma e2 UInt ct blockchain
        with TypeMismatch _ -> 
          begin 
            typecheck gamma e1 (Address None) ct blockchain;
            typecheck gamma e2 (Address None) ct blockchain
          end 
      end *)
    | Greater (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | GreaterOrEquals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Lesser (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | LesserOrEquals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Inequals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    in 
  match e with
  | Val _ -> axioms gamma e  
  | AritOp a -> infer_arit gamma a ct 
  | BoolOp b -> infer_bool gamma b ct 
  | Revert -> axioms gamma e 
  | Balance e1 -> 
    let t_e1 = infer_type gamma c1 ct in 
    begin match t_e1 with 
      | Address _ -> UInt
      | C _ -> UInt
      | _ -> Error(type_infer_error Address)
    end
  | Address e1 -> 
    begin match t with 
      | Address (Some CTop) -> typecheck gamma e1 CTop ct blockchain
      | Address (Some (C i)) -> typecheck gamma e1 (C i) ct blockchain
      | _ -> raise (TypeMismatch (Address (Some CTop), t))
    end 
  | Return e1 -> 
    let t_e1 = infer_type gamma e1 ct in
    t_e1
  | Seq (e1, e2) ->
    (* inferencia *)
    let t_e2 = infer_type gamma e2 ct in 
    t_e2
  | _ -> assert false

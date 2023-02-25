open Types 
open Utils

let axioms (gamma: gamma) (e: expr) (t: t_exp) : unit = match e,t with 
  | Val (VBool _), Bool -> ()  
  | Val (VBool _), _ -> raise (TypeMismatch (Bool, t))
  | Val (VUInt n), UInt -> if n >= 0 then () else raise (TypeMismatch (UInt, t))
  | Val (VUInt _), _ -> raise (TypeMismatch (UInt, t))
  | Revert, _ -> ()
  | Val (VUnit), Unit -> ()
  | Val (VUnit), _ -> raise (TypeMismatch (Unit, t))
  | Val (VAddress _), Address -> ()
  | Val (VAddress _), _ -> raise (TypeMismatch (Address, t))
  | Val (VContract _), C -1 -> ()
  | Val (VContract n), C y -> if n <> y then raise (TypeMismatch (C (y), t)) else ()
  | Val (VContract n), _ -> raise (TypeMismatch (C (n), t))
  | MsgSender, Address -> ()
  | MsgSender, _ -> raise (TypeMismatch (Address, t))
  | MsgValue, UInt -> ()
  | MsgValue, _ -> raise (TypeMismatch (UInt, t))
  | Var x, t -> 
    let t_x = Hashtbl.find gamma x in
    if t_x <> t then raise (TypeMismatch (t_x, t))
    else ()
  | _ -> assert false

let compareType (t1: t_exp) (t2: t_exp) : bool = 
  t1 = t2 || t1 = TRevert || t2 = TRevert 

let rec typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) (blockchain: blockchain) : unit = match e with 
  | Val (VBool _) -> axioms gamma e t
  | Val (VUInt _) -> axioms gamma e t
  | Val (VUnit) -> axioms gamma e t
  | Val (VAddress _) -> axioms gamma e t
  | Val (VContract _) -> axioms gamma e t
  | Val (VMapping (m, t_exp)) -> 
    let (t1, t2) = match t with 
      | Map (t1, t2) -> (t1, t2)
      | _ -> raise (TypeMismatch (Map (t_exp, t_exp), t)) (* first hand of tuple, how to know what value should we have? *)
    in 
    Hashtbl.iter (fun k v -> typecheck gamma k t1 ct blockchain; typecheck gamma v t2 ct blockchain) m
  | Var _ -> axioms gamma e t
  | AritOp a -> begin match a with 
      | Plus (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct blockchain ;
        typecheck gamma e2 UInt ct blockchain
      | Div (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | Times (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct blockchain ;
        typecheck gamma e2 UInt ct blockchain
      | Minus (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | Exp (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | Mod (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
    end
  | BoolOp b -> begin match b with 
      | Neg e1 -> 
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 Bool ct blockchain
      | Conj (e1, e2) -> 
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 Bool ct blockchain;
        typecheck gamma e2 Bool ct blockchain
      | Disj (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 Bool ct blockchain;
        typecheck gamma e2 Bool ct blockchain
      | Equals (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | Greater (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | GreaterOrEquals (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | Lesser (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | LesserOrEquals (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
      | Inequals (e1, e2) ->
        if t <> Bool then 
          raise (TypeMismatch (Bool, t));
        typecheck gamma e1 UInt ct blockchain;
        typecheck gamma e2 UInt ct blockchain
    end
  | Revert -> axioms gamma e t 
  | Balance e1 -> 
    if t <> UInt then 
      raise (TypeMismatch (UInt, t));
    typecheck gamma e1 Address ct blockchain;
  | Address e1 -> 
    if t <> Address then 
      raise (TypeMismatch (Address, t));
    typecheck gamma e1 (C(-1)) ct blockchain;
  | Return e1 -> typecheck gamma e1 t ct blockchain 
  | Seq (_, e2) ->
    typecheck gamma e2 t ct blockchain
  | MsgSender -> 
    axioms gamma e t  
  | MsgValue ->
    axioms gamma e t  
  | If (e1, e2, e3) -> 
    typecheck gamma e1 Bool ct blockchain;
    typecheck gamma e2 t ct blockchain;
    typecheck gamma e3 t ct blockchain;
  | Assign (s, e1) -> 
    let t_x = Hashtbl.find gamma s in
    typecheck gamma e1 t_x ct blockchain 
  (* how do we know what type we are expect blockchaining for our map? what are the values for t1 and t2? *)
  (* | MapRead (e1, e2) ->  
     | MapWrite (e1, e2, e3) -> *)
  | Transfer (e1, e2) ->
    if t <> Unit then 
      raise (TypeMismatch (Unit, t));
    typecheck gamma e2 UInt ct blockchain;
    typecheck gamma e1 Address ct blockchain
  | New (s, e, le) ->
    (* type check contract blockchain ...*)
    if t <> (C(-1)) then 
      raise (TypeMismatch (C(-1), t));
    typecheck gamma e UInt ct blockchain;
    let c_def: contract_def = Hashtbl.find ct s in
    let (ts, _) = function_type c_def.name "constructor" ct in
    List.iter2 (fun t_cx e_cx -> typecheck gamma e_cx t_cx ct blockchain ) ts le;
    (* Verify all parameters have same type to the ones defined in the contract blockchain construct blockchainor*)
    (* | Call (e1, s, e2, le) -> 
       (* e1 should always point to a contract, however it can be also a Var x || this.sv pointing to a contract *)
       typecheck gamma e1 (C(-1, "")) ct blockchain;
       typecheck gamma e2 UInt ct blockchain;
       () *)
    (* Bank(address) *)
  | Cons (_s, e1) -> 
    (* e1 is always an address, however it can be a Val (Address a) || MsgSender || Var x || this.sv *)
    (* we need to make sure that s == cname, thus we need to access the contract stored in the blockchain*)
    typecheck gamma e1 Address ct blockchain;
    (* get_contract_by_address blockchain a*)
    (* typecheck gamma e (C(-1)) ct blockchain *)
    (* | CallTopLevel (e1, s, e2, e3, le) -> 
       typecheck gamma e1 (C(-1, "")) ct blockchain;
       typecheck gamma e2 UInt ct blockchain;
       typecheck gamma e3 Address ct blockchain;  *)
  | Let (t_e, s, e1, e2) -> 
    typecheck gamma e1 t_e ct blockchain;
    Hashtbl.add gamma s t_e;
    typecheck gamma e2 t ct blockchain;
    (* typecheck e2 with ???*)
  | _ -> assert false
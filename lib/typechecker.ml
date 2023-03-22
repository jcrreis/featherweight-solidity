open Types 
(* open Utils *)
(* open C3  *)

let axioms (gamma: gamma) (e: expr) (t: t_exp) : unit = match e,t with 
  | Val (VBool _), Bool -> ()  
  | Val (VBool _), _ -> raise (TypeMismatch (Bool, t))
  | Val (VUInt n), UInt -> if n >= 0 then () else raise (TypeMismatch (UInt, t))
  | Val (VUInt _), _ -> raise (TypeMismatch (UInt, t))
  | Revert, _ -> ()
  | Val (VUnit), Unit -> ()
  | Val (VUnit), _ -> raise (TypeMismatch (Unit, t))
  | Val (VAddress a), _ -> 
    begin 
      try 
        let a = Hashtbl.find gamma (Val (VAddress a)) in 
        begin match t,a with 
          | Address CTop, Address _ -> ()
          | Address (C i), Address CTop -> raise (TypeMismatch (C i, CTop))
          | Address (C i), Address (C i') -> if i = i' then () else raise (TypeMismatch (C i, C i'))
          | _ -> raise (TypeMismatch (a, t))
        end 
      with Not_found -> raise (UnboundVariable a)
    end
  | Val (VContract i), _ ->
    begin 
      try 
        let c = Hashtbl.find gamma (Val (VContract i)) in 
        begin match t, c with 
          | CTop, CTop -> ()
          | CTop, C _ -> () 
          | C _, CTop -> raise (TypeMismatch (c, t)) 
          | C i, C i' -> if i <> i' then raise (TypeMismatch (c, t)) else ()
          | _ -> raise (TypeMismatch (c, t)) 
        end 
      with Not_found -> raise (UnboundVariable "")
    end 
  | MsgSender, Address CTop -> ()
  | MsgSender, t -> 
    begin 
      try 
        let t_x = Hashtbl.find gamma (MsgSender) in
        if t_x <> t then raise (TypeMismatch (t_x, t))
        else ()
      with Not_found -> raise (UnboundVariable "msg.sender")
    end 
  (*
  | MsgSender, Address (Some _s) -> assert false
  | MsgSender, _ -> raise (TypeMismatch (Address CTop, t)) *)
  | MsgValue, UInt -> ()
  | MsgValue, _ -> raise (TypeMismatch (UInt, t))
  | Var x, t -> 
    begin 
      try 
        let t_x = Hashtbl.find gamma (Var x) in
        if t_x <> t then raise (TypeMismatch (t_x, t))
        else ()
      with Not_found -> raise (UnboundVariable x)
    end 
  | _ -> assert false

let compareType (t1: t_exp) (t2: t_exp) : bool = 
  match t1, t2 with 
    | Address CTop, Address _ -> true
    | Address (C _), Address CTop -> false
    | Address (C i), Address (C i') -> if i = i' then true else false
    | CTop, CTop -> true
    | CTop, C _ -> true 
    | C _, CTop -> false
    | C i, C i' -> if i <> i' then false else true
    | _ -> t1 = t2

let rec typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) (blockchain: blockchain) : unit = match e with 
  | Val (VBool _) -> axioms gamma e t
  | Val (VUInt _) -> axioms gamma e t
  | Val (VUnit) -> axioms gamma e t
  | Val (VAddress _) -> axioms gamma e t
  | Val (VContract _) -> axioms gamma e t
  | Val (VMapping (m, t_exp)) -> 
    let map_t = Hashtbl.find gamma (Val(VMapping(m, t_exp))) in  
    begin match t, map_t with
      | Map (t1, t2), Map (t3, t4) -> 
          if compareType t1 t3 && compareType t2 t4 then 
            Hashtbl.iter (fun k v -> typecheck gamma k t1 ct blockchain; typecheck gamma v t2 ct blockchain) m
          else
            raise (TypeMismatch (map_t, t))
      | _ -> raise (TypeMismatch (map_t, t))
    end
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
    typecheck gamma e1 (Address CTop) ct blockchain;
  | Address e1 -> 
    begin match t with 
      | Address CTop -> typecheck gamma e1 CTop ct blockchain
      | Address (C i) -> typecheck gamma e1 (C i) ct blockchain 
      | _ -> raise (TypeMismatch (Address CTop, t))
    end 
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
      typecheck gamma (Var s) t ct blockchain;
      typecheck gamma e1 t ct blockchain
  (* how do we know what type we are expect blockchaining for our map? what are the values for t1 and t2? *)
  | MapRead (_e1, _e2) ->  
    (* typecheck gamma e1 (Map ()) ct blockchain; *)
    assert false
  | MapWrite (_e1, _e2, _e3) -> assert false 
  | StateRead (e1, s) -> 
    begin 
      try 
        let t_x = Hashtbl.find gamma (StateRead(e1, s)) in 
        typecheck gamma e1 t_x ct blockchain
      with Not_found -> raise (UnboundVariable ("State Var " ^ s)) 
    end 
  | StateAssign (e1, s, e2) -> 
        typecheck gamma (StateRead(e1, s)) t ct blockchain;
        typecheck gamma e2 t ct blockchain
  | Transfer (e1, e2) ->
    if t <> Unit then 
      raise (TypeMismatch (Unit, t));
    typecheck gamma e2 UInt ct blockchain;
    typecheck gamma e1 (Address CTop) ct blockchain
  | New (s, e, le) ->
    (* type check contract blockchain ...*)
    if t <> (CTop) then 
      raise (TypeMismatch (CTop, t));
    typecheck gamma e UInt ct blockchain;
    let c_def: contract_def = Hashtbl.find ct s in
    let (args, _) = c_def.constructor in 
    let ts = List.map (fun (t_e, _) -> t_e) args in
    List.iter2 (fun t_cx e_cx -> typecheck gamma e_cx t_cx ct blockchain ) ts le;
    (* Verify all parameters have same type to the ones defined in the contract blockchain construct blockchainor*)
    (* | Call (e1, s, e2, le) -> 
       (* e1 should always point to a contract, however it can be also a Var x || this.sv pointing to a contract *)
       typecheck gamma e1 (C(-1, "")) ct blockchain;
       typecheck gamma e2 UInt ct blockchain;
       () 
    *)
    (* Bank(address) *)
  | Cons (_s, e1) -> 
    (* e1 is always an address, however it can be a Val (Address a) || MsgSender || Var x || this.sv *)
    (* we need to make sure that s == cname, thus we need to access the contract stored in the blockchain*)
    typecheck gamma e1 (Address (CTop)) ct blockchain;
    (* get_contract_by_address blockchain a*)
    (* typecheck gamma e (C(-1)) ct blockchain *)
    (* | CallTopLevel (e1, s, e2, e3, le) -> 
       typecheck gamma e1 (C(-1, "")) ct blockchain;
       typecheck gamma e2 UInt ct blockchain;
       typecheck gamma e3 Address ct blockchain;  *)
  | Let (t_e, s, e1, e2) -> 
    typecheck gamma e1 t_e ct blockchain;
    Hashtbl.add gamma (Var s) t_e;
    typecheck gamma e2 t ct blockchain;
    (* typecheck e2 with ???*)
  | _ -> assert false
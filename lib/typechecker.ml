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

let rec typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) : unit = match e with 
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
    Hashtbl.iter (fun k v -> typecheck gamma k t1 ct; typecheck gamma v t2 ct) m
  | Var _ -> axioms gamma e t
  | AritOp a -> begin match a with 
    | Plus (e1, e2) -> 
      if t <> UInt then 
        raise (TypeMismatch (UInt, t));
      typecheck gamma e1 UInt ct ;
      typecheck gamma e2 UInt ct
    | Div (e1, e2) -> 
      if t <> UInt then 
        raise (TypeMismatch (UInt, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
      | Times (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct ;
        typecheck gamma e2 UInt ct
      | Minus (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct;
        typecheck gamma e2 UInt ct
      | Exp (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct;
        typecheck gamma e2 UInt ct
      | Mod (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt ct;
        typecheck gamma e2 UInt ct
  end
  | BoolOp b -> begin match b with 
    | Neg e1 -> 
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 Bool ct
    | Conj (e1, e2) -> 
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 Bool ct;
      typecheck gamma e2 Bool ct
    | Disj (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 Bool ct;
      typecheck gamma e2 Bool ct
    | Equals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
    | Greater (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
    | GreaterOrEquals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
    | Lesser (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
    | LesserOrEquals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
    | Inequals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt ct;
      typecheck gamma e2 UInt ct
  end
  | Revert -> axioms gamma e t 
  | Balance e1 -> 
    if t <> UInt then 
      raise (TypeMismatch (UInt, t));
    typecheck gamma e1 Address ct;
  | Address e1 -> 
    if t <> Address then 
      raise (TypeMismatch (Address, t));
    typecheck gamma e1 (C(-1)) ct;
  | Return e1 -> typecheck gamma e1 t ct 
  | Seq (_, e2) ->
    typecheck gamma e2 t ct
  | MsgSender -> 
    axioms gamma e t  
  | MsgValue ->
    axioms gamma e t  
  | If (e1, e2, e3) -> 
    typecheck gamma e1 Bool ct;
    typecheck gamma e2 t ct;
    typecheck gamma e3 t ct;
  | Assign (s, e1) -> 
    let t_x = Hashtbl.find gamma s in
    typecheck gamma e1 t_x ct 
    (* how do we know what type we are expecting for our map? what are the values for t1 and t2? *)
  (* | MapRead (e1, e2) ->  
  | MapWrite (e1, e2, e3) -> *)
  | Transfer (e1, e2) ->
    if t <> Unit then 
      raise (TypeMismatch (Unit, t));
    typecheck gamma e2 UInt ct;
    typecheck gamma e1 Address ct
  | New (s, e, le) ->
    (* type check contract ...*)
    if t <> (C(-1)) then 
      raise (TypeMismatch (C(-1), t));
    typecheck gamma e UInt ct;
    let c_def: contract_def = Hashtbl.find ct s in
    let (ts, _) = function_type c_def.name "constructor" ct in
    List.iter2 (fun t_cx e_cx -> typecheck gamma e_cx t_cx ct ) ts le;
    (* Verify all parameters have same type to the ones defined in the contract constructor*)
  (* | Call (e1, s, e2, le) -> 
    typecheck gamma e1 (C(-1, "")) ct;
    typecheck gamma e2 UInt ct;
    () *)
  | Cons (_, e1) -> 
    typecheck gamma e1 Address ct;
    typecheck gamma e (C(-1)) ct
  (* | CallTopLevel (e1, s, e2, e3, le) -> 
    typecheck gamma e1 (C(-1, "")) ct;
    typecheck gamma e2 UInt ct;
    typecheck gamma e3 Address ct;  *)
  | Let (t_e, s, e1, e2) -> 
    typecheck gamma e1 t_e ct;
    Hashtbl.add gamma s t_e;
    typecheck gamma e2 t ct;
    (* typecheck e2 with ???*)
  | _ -> assert false
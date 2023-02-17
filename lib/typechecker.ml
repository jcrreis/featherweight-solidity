open Types 


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
  | Val (VContract _n), C _y -> ()
  | Val (VContract n), _ -> raise (TypeMismatch (C n, t))
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
  (* ((expr, expr) Hashtbl.t ) * t_exp *)
  (* | Map of t_exp * t_exp *)

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
  | Address _e1 -> 
    if t <> Address then 
      raise (TypeMismatch (Address, t))
    (* let t = typecheck gamma e1 in  *)
    (* begin match t with 
      | C _ -> Address 
      | _ -> assert false 
    end *)
    else
      assert false
  | Return e1 -> typecheck gamma e1 t ct 
  | Seq (_, e2) ->
    typecheck gamma e2 t ct
  | If (e1, e2, e3) -> 
    typecheck gamma e1 Bool ct;
    typecheck gamma e2 t ct;
    typecheck gamma e3 t ct
  | Assign (s, e1) -> 
    let t_x = Hashtbl.find gamma s in
    typecheck gamma e1 t_x ct 
    (* how do we know what type we are expecting for our map? what are the values for t1 and t2? *)
  (* | MapRead (e1, e2) ->  
  | MapWrite (e1, e2, e3) -> *)
  | Transfer (e1, e2) ->
    typecheck gamma e2 UInt ct;
    typecheck gamma e1 Address ct
  | New (s, e, le) ->
    typecheck gamma e UInt ct;
    let c_def: contract_def = Hashtbl.find ct s in
    let (ts, _) = c_def.constructor in
    List.iter2 (fun (t_cx, _) e_cx -> typecheck gamma e_cx t_cx ct ) ts le; (* Verify all parameters have same type to the ones defined in the contract constructor*)
  (* | Const (s, e1) ->  *) (* CASTING CONTRACTS MIGHT BE A PROBLEM! ALWAYS THROW A WARNING *)
  | _ -> assert false

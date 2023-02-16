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


let rec typecheck (gamma: gamma) (e: expr) (t: t_exp) : unit = match e with 
  | Val (VBool _) -> axioms gamma e t
  | Val (VUInt _) -> axioms gamma e t
  | Val (VUnit) -> axioms gamma e t
  | Val (VAddress _) -> axioms gamma e t
  | Val (VContract _) -> axioms gamma e t
  | Var _ -> axioms gamma e t
  | AritOp a -> begin match a with 
    | Plus (e1, e2) -> 
      if t <> UInt then 
        raise (TypeMismatch (UInt, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
    | Div (e1, e2) -> 
      if t <> UInt then 
        raise (TypeMismatch (UInt, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
      | Times (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt;
        typecheck gamma e2 UInt
      | Minus (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt;
        typecheck gamma e2 UInt
      | Exp (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt;
        typecheck gamma e2 UInt
      | Mod (e1, e2) -> 
        if t <> UInt then 
          raise (TypeMismatch (UInt, t));
        typecheck gamma e1 UInt;
        typecheck gamma e2 UInt
  end
  | BoolOp b -> begin match b with 
    | Neg e1 -> 
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 Bool
    | Conj (e1, e2) -> 
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 Bool;
      typecheck gamma e2 Bool
    | Disj (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 Bool;
      typecheck gamma e2 Bool
    | Equals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
    | Greater (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
    | GreaterOrEquals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
    | Lesser (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
    | LesserOrEquals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
    | Inequals (e1, e2) ->
      if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      typecheck gamma e1 UInt;
      typecheck gamma e2 UInt
  end
  | Revert -> axioms gamma e t 
  | Balance e1 -> 
    if t <> UInt then 
      raise (TypeMismatch (UInt, t));
    typecheck gamma e1 Address;
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
  | Return e1 -> typecheck gamma e1 t
  | Seq (_, e2) ->
    typecheck gamma e2 t
  | If (e1, e2, e3) -> 
    typecheck gamma e1 Bool;
    typecheck gamma e2 t;
    typecheck gamma e3 t
  | Assign (s, e1) -> 
    let t_x = Hashtbl.find gamma s in
    typecheck gamma e1 t_x
  | _ -> assert false

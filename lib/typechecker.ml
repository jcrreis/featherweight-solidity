open Types 

let axioms (gamma: gamma) (e: expr) : t_exp = match e with 
  | Val(VBool _) -> Bool  
  | Val (VUInt n) -> if n >= 0 then UInt else assert false
  | Revert -> TRevert
  | Val (VUnit) -> Unit
  | Val (VAddress _) -> Address
  | Val (VContract n) -> C n
  | Var x -> Hashtbl.find gamma x
  | _ -> assert false

let compareType (t1: t_exp) (t2: t_exp) : bool = 
  if t1 = t2 || t1 = TRevert || t2 = TRevert 
    then true 
  else false


let rec typecheck (gamma: gamma) (e: expr) : t_exp = match e with 
  | Val (VBool _) -> axioms gamma e
  | Val (VUInt _) -> axioms gamma e
  | Val (VUnit) -> axioms gamma e
  | Val (VAddress _) -> axioms gamma e
  | Val (VContract _) -> axioms gamma e
  | Var _ -> axioms gamma e
  | AritOp a -> begin match a with 
    | Plus (e1, e2) -> 
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt then 
        UInt
      else
        assert false 
    | Div (e1, e2) -> 
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt then 
        UInt
      else
        assert false 
      | Times (e1, e2) -> 
        let t1 = typecheck gamma e1 in 
        let t2 = typecheck gamma e2 in 
        if t1 = UInt && t2 = UInt then 
          UInt
        else
          assert false 
      | Minus (e1, e2) -> 
        let t1 = typecheck gamma e1 in 
        let t2 = typecheck gamma e2 in 
        if t1 = UInt && t2 = UInt then 
          UInt
        else
          assert false 
      | Exp (e1, e2) -> 
        let t1 = typecheck gamma e1 in 
        let t2 = typecheck gamma e2 in 
        if t1 = UInt && t2 = UInt then 
          UInt
        else
          assert false 
      | Mod (e1, e2) -> 
        let t1 = typecheck gamma e1 in 
        let t2 = typecheck gamma e2 in 
        if t1 = UInt && t2 = UInt then 
          UInt
        else
          assert false 
  end
  | BoolOp b -> begin match b with 
    | Neg e1 -> 
      let t1 = typecheck gamma e1 in 
      if t1 = Bool 
        then Bool 
      else
        assert false
    | Conj (e1, e2) -> 
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = Bool && t2 = Bool  
        then Bool 
      else
        assert false
    | Disj (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = Bool && t2 = Bool  
        then Bool 
      else
        assert false
    | Equals (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt  
        then Bool 
      else
        assert false
    | Greater (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt  
        then Bool 
      else
        assert false
    | GreaterOrEquals (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt  
        then Bool 
      else
        assert false
    | Lesser (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt  
        then Bool 
      else
        assert false
    | LesserOrEquals (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt  
        then Bool 
      else
        assert false
    | Inequals (e1, e2) ->
      let t1 = typecheck gamma e1 in 
      let t2 = typecheck gamma e2 in 
      if t1 = UInt && t2 = UInt  
        then Bool 
      else
        assert false
  end
  | Revert -> axioms gamma e
  | Balance e1 -> let t = typecheck gamma e1 in 
    if compareType t Address 
      then UInt 
    else 
      assert false
  | Address e1 -> 
    let t = typecheck gamma e1 in 
    begin match t with 
      | C _ -> Address 
      | _ -> assert false 
    end
  | Return e1 -> typecheck gamma e1 
  | Seq (_, e2) ->  
    let t2 = typecheck gamma e2 in 
    t2
  | If (e1, e2, e3) -> 
    let t1 = typecheck gamma e1 in  
    if t1 = Bool then 
      begin 
      let t2 = typecheck gamma e2 in 
      let t3 = typecheck gamma e3 in 
      if compareType t2 t3 
        then t2
      else assert false
      end 
    else assert false 
  | Assign (s, e1) -> 
    let t_s = Hashtbl.find gamma s in 
    let t1 = typecheck gamma e1 in 
    if t_s = t1 
      then t_s
    else
      assert false   
  | _ -> assert false

open Types 

let axioms (e: expr) : t_exp = match e with 
  | Val(VBool _) -> Bool  
  | Val (VUInt n) -> if n >= 0 then UInt else assert false
  | Revert -> TRevert
  | Val (VUnit) -> Unit
  | Val (VAddress _) -> Address
  | Val (VContract n) -> C n
  | _ -> assert false

let compareType (t1: t_exp) (t2: t_exp) : bool = 
  if t1 = t2 || t1 = TRevert || t2 = TRevert 
    then true 
  else false

let rec typecheck (gamma: gamma) (e: expr) : t_exp = match e with 
  | Val (VBool _) -> axioms e
  | Val (VUInt _) -> axioms e
  | Val (VUnit) -> axioms e
  | Val (VAddress _) -> axioms e
  | Val (VContract _) -> axioms e
  | Revert -> axioms e
  | Var x -> Hashtbl.find gamma x
  | Balance e1 -> let t = typecheck gamma e1 in 
    if compareType t Address 
      then UInt 
    else 
      assert false
  | Address e1 -> 
    let t = typecheck gamma e1 in 
    if compareType t (C 0) (* TODO ---- *)
      then Address 
    else 
      assert false
  | Return e1 -> typecheck gamma e1 
  (* | Seq (e1, e2) ->  
    let t1 = typecheck gamma e1 in 
    let t2 = typecheck gamma e2 in 
    if compareType t1 Unit && compareType t2 Unit 
      then Unit 
    else 
      assert false *)
  | _ -> assert false

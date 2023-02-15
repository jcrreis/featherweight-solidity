open Types

let axioms (e: expr) : t_exp = match e with 
  | Val(VBool _) -> Bool  
  | Val (VUInt n) -> if n >= 0 then UInt else assert false
  | Revert -> TRevert
  | Val (VUnit) -> Unit
  | _ -> assert false

let rec typecheck (gamma: gamma) (e: expr) : t_exp = match e with 
  | Val (VBool _) -> axioms e
  | Val (VUInt _) -> axioms e
  | Val (VUnit) -> axioms e
  | Var x -> Hashtbl.find gamma x
  | _ -> assert false
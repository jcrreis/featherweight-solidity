open Types

let axioms (e: expr) : t_exp = match e with 
  | Val(VBool _) -> Bool  
  | Val (VUInt n) -> if n >= 0 then UInt else assert false
  | Revert -> TRevert
  | Val (VUnit) -> Unit
  | _ -> assert false

let _typecheck = assert false 
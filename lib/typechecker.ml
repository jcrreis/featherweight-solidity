open Types 
open Utils
open C3 
open Pprinters 

let rec compareType (t1: t_exp) (t2: t_exp) (ct: contract_table) : bool = 
  match t1, t2 with 
  | Address _, Address CTop -> true
  | Address CTop, Address _ -> false
  | Address (C name1), Address (C name2) -> 
    compareType (C name1) (C name2) ct
  | CTop, CTop -> true
  | CTop, C _ -> false 
  | C _, CTop -> true
  | C name1, C name2 -> 
    let contract_def: contract_def = Hashtbl.find ct name2 in
    let contract_hierarchy: string list = match c3_linearization contract_def with 
      | Ok v -> v
      | _ -> assert false 
    in
    if List.mem name1 contract_hierarchy then true else false
  | _ -> t1 = t2


let axioms (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) : unit = match e,t with 
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
        (* gamma_vars * gamma_addresses * gamma_contracts *)
        let (_, gamma_addresses, _) = gamma in 
        let a = Hashtbl.find gamma_addresses (VAddress a) in 
        if compareType a t ct then () else raise (TypeMismatch (a, t))
      with Not_found -> raise (UnboundVariable a)
    end
  | Val (VContract i), _ ->
    begin 
      try 
        let (_, _, gamma_contracts) = gamma in 
        let c = Hashtbl.find gamma_contracts (VContract i) in 
        if compareType c t ct then () else raise (TypeMismatch (c, t))
      with Not_found -> raise (UnboundVariable "")
    end 
  | MsgSender, Address CTop -> ()
  | MsgSender, t -> 
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars "msg.sender" in
        if compareType t_x t ct then () else raise (TypeMismatch (t_x, t))
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
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars x in
        if compareType t_x t ct then () else raise (TypeMismatch (t_x, t))
      with Not_found -> raise (UnboundVariable x)
    end 
  | _ -> assert false

(* return (t_exp, string) result ??? *)
let rec infer_type (g: gamma) (e: expr) (ct: contract_table) : t_exp = match e with 
  | Val (VBool _) -> Bool
  | Val (VUInt _) -> UInt
  | Val (VUnit) -> Unit
  | Val (VAddress a) -> 
    begin 
      try 
        let (_, gamma_addresses, _) = g in 
        let a = Hashtbl.find gamma_addresses (VAddress a) in 
        a
      with Not_found -> raise (UnboundVariable "")
    end  
  | Val (VMapping (_m, _t_exp)) -> 
    assert false
    (* Hashtbl.iter (fun k v -> typecheck gamma k t1 ct blockchain; 
                       typecheck gamma v t2 ct blockchain) m
    begin match t with 
      | Map (t1, t2) -> 
        (* C name ; Address name*)
        ;
        if compareType t_exp t2 ct then () else raise (TypeMismatch (t_exp, t2))
      | _ -> raise (TypeMismatch (Map(UInt, t_exp), t))
    end *)
  | Var s -> 
    begin 
      try 
        let (gamma_vars, _, _) = g in 
        let t_x = Hashtbl.find gamma_vars s in
        t_x
      with Not_found -> raise (UnboundVariable s)
    end  
  | Val (VContract i) -> 
    begin 
      try 
        let (_, _, gamma_contracts) = g in 
        let c = Hashtbl.find gamma_contracts (VContract i) in 
        c
      with Not_found -> raise (UnboundVariable "")
    end  
  | AritOp a -> begin match a with 
      | Plus (e1, e2) -> 
        begin 
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> UInt
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Div (e1, e2) -> 
        begin 
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> UInt
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Times (e1, e2) -> 
        begin 
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> UInt
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Minus (e1, e2) -> 
        begin 
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> UInt
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Exp (e1, e2) -> 
        begin 
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> UInt
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Mod (e1, e2) -> 
        begin 
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> UInt
          | _ -> raise (Failure "Não consegui inferir") 
        end
    end
  | BoolOp b -> begin match b with 
      | Neg e1 -> 
        let t_e1 : t_exp = infer_type g e1 ct in 
        if t_e1 = Bool then Bool else raise (Failure "Não consegui inferir") 
      | Conj (e1, e2) -> 
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | Bool, Bool -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Disj (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | Bool, Bool -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Equals (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> Bool
          | Address _, Address _ -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Greater (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | GreaterOrEquals (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Lesser (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | LesserOrEquals (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
      | Inequals (e1, e2) ->
        begin  
          let t_e1 : t_exp = infer_type g e1 ct in 
          let t_e2 : t_exp = infer_type g e2 ct in 
          match t_e1, t_e2 with 
          | UInt, UInt -> Bool
          | _ -> raise (Failure "Não consegui inferir") 
        end
    end
  | Revert -> TRevert
  | This None -> 
    begin 
      try 
        let (gamma_vars, _, _) = g in 
        let t_x = Hashtbl.find gamma_vars "this" in
        t_x
      with Not_found -> raise (UnboundVariable "this")
    end 
  | Balance e1 ->  
    begin 
      let t_e1 : t_exp = infer_type g e1 ct in 
      match t_e1 with 
      | C _ -> UInt 
      | Address _ -> UInt
      (* CTop, C "Bank" C ".." C ("..")*)
      | _ -> raise (Failure "Não consegui inferir") 
    end
  | Address e1 -> 
    begin
      let t_e1 : t_exp = infer_type g e1 ct in 
      match t_e1 with 
      | CTop -> Address CTop 
      | C name -> Address (C name)
      | Address t_e -> Address t_e
      | _ -> raise (Failure "Não consegui inferir") 
    end 
  | Seq (_, e2) ->
    let t_e2 : t_exp = infer_type g e2 ct in 
    t_e2 
  | MsgSender -> 
    begin 
      try 
        let (gamma_vars, _, _) = g in 
        let t_x = Hashtbl.find gamma_vars "msg.sender" in
        t_x
      with Not_found -> raise (UnboundVariable "msg.sender")
    end 
  | MsgValue ->
    begin 
      try 
        let (gamma_vars, _, _) = g in 
        let t_x = Hashtbl.find gamma_vars "msg.value" in
        t_x
      with Not_found -> raise (UnboundVariable "msg.sender")
    end  
  | If (e1, e2, e3) -> 
    begin
      let t_e1 : t_exp = infer_type g e1 ct in 
      if t_e1 <> Bool then raise (Failure "Não consegui inferir") 
      else 
        begin 
          let t_e2 : t_exp = infer_type g e2 ct in 
          let t_e3 : t_exp = infer_type g e3 ct in 
          if t_e2 = t_e3 then t_e2 else raise (Failure "Não consegui inferir") 
        end 
    end
  | Assign (_s, _e1) -> 
    assert false 
  | Transfer (e1, e2) ->
    begin 
      let t_e1 : t_exp = infer_type g e1 ct in 
      let t_e2 : t_exp = infer_type g e2 ct in 
      match t_e1, t_e2 with 
        | Address _, UInt -> Unit
        | _ -> raise (Failure "Não consegui inferir")  
    end
  | MapRead (e1, e2) ->  
    begin
      let t_e1 : t_exp = infer_type g e1 ct in 
      let _t_e2 : t_exp = infer_type g e2 ct in 
      match t_e1 with 
        | Map (_t1, _t2) -> 
          begin match e1 with 
            | Val(VMapping (_, _t_exp)) -> 
              assert false 
            | _ -> raise (Failure "Não consegui inferir")  
          end 
        | _ -> raise (Failure "Não consegui inferir")  
    end
  | MapWrite _ ->
    Unit
      (* | Val(VMapping (_, t_exp)) ->
        (* how do we know t1? *)
        typecheck gamma e1 (Map (UInt , t)) ct blockchain;
        typecheck gamma e2 UInt ct blockchain;
        if compareType t_exp t ct then () 
        else raise (TypeMismatch (t_exp, t))
      | _ -> raise (TypeMismatch (t, t)) *)  (* | MapWrite (e1, e2, e3) ->
    begin match t with 
      | Map(t1, t2) ->
        typecheck gamma e1 t ct blockchain;
        typecheck gamma e2 t1 ct blockchain;
        typecheck gamma e3 t2 ct blockchain;
      | _ -> raise (TypeMismatch (Map(UInt, t), t))
    end
  | StateRead (e1, s) -> (*VER*)
    begin 
      typecheck gamma e1 CTop ct blockchain;
      let t_e : t_exp = infer_type gamma e1 ct in  
      let cname : string = match t_e with 
        | C name -> name 
        | Address (C name) -> name 
        | _ -> assert false 
      in
      let sv : (t_exp * string) list = state_vars_contract cname ct in 
      try
        let (t_e, _s) = List.find (fun (_, e_s) -> e_s = s) sv in 
        if compareType t_e t ct then () else raise (TypeMismatch (t_e, t))
      with Not_found -> raise (UnboundVariable "s")
    end
  | StateAssign (e1, s, e2) -> 
    typecheck gamma (StateRead (e1, s)) t ct blockchain;
    typecheck gamma e2 t ct blockchain; *)

  | StateRead (e1, s) -> (*VER*)
    begin 
      let t_e : t_exp = infer_type g e1 ct in  
      let cname : string = match t_e with 
        | C name -> name 
        | Address (C name) -> name 
        | _ -> raise (Failure "Não consegui inferir")  
      in
      let sv : (t_exp * string) list = state_vars_contract cname ct in 
      try
        let (t_e, _s) = List.find (fun (_, e_s) -> e_s = s) sv in 
        t_e
      with Not_found -> raise (UnboundVariable ((expr_to_string e1) ^ s))
    end
  | StateAssign _ -> 
    Unit
  | New (s, e, le) ->
    (* type check contract blockchain ...*)
    begin
      let t_e : t_exp = infer_type g e ct in 
      if t_e <> UInt then 
        raise (Failure "Não consegui inferir")  
      else 
        begin 
          let c_def: contract_def = Hashtbl.find ct s in
          let (args, _) = c_def.constructor in 
          let ts = List.map (fun (t_e, _) -> t_e) args in
          List.iter2 (fun t_cx e_cx -> 
            let t_ecx : t_exp = infer_type g e_cx ct in 
            if t_cx <> t_ecx then raise (Failure "Não consegui inferir") else ()) 
            ts le;
          C s 
        end
    end
  | Cons (s, e1) -> 
    (* e1 is always an address, however it can be a Val (Address a) || MsgSender || Var x || this.sv *)
    (* we need to make sure that s == cname, thus we need to access the contract stored in the blockchain*)
    begin
      let t_e1 : t_exp = infer_type g e1 ct in 
      match t_e1 with 
        | Address t_exp ->
          begin match t_exp with 
            | C name -> 
              begin 
                let res : bool = compareType (C name) (C s) ct in 
                if res then (C name) else raise (Failure "Não consegui inferir") 
              end
            | _ -> raise (Failure "Não consegui inferir")  
          end
        | _ -> raise (Failure "Não consegui inferir")  
    end
  | _ -> assert false 

let rec typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) (blockchain: blockchain) : unit = match e with 
  | Val (VBool _) -> axioms gamma e t ct
  | Val (VUInt _) -> axioms gamma e t ct
  | Val (VUnit) -> axioms gamma e t ct
  | Val (VAddress _) -> axioms gamma e t ct
  | Val (VContract _) -> axioms gamma e t ct
  | Val (VMapping (m, t_exp)) -> 
    begin match t with 
      | Map (t1, t2) -> 
        (* C name ; Address name*)
        Hashtbl.iter (fun k v -> typecheck gamma k t1 ct blockchain; 
                       typecheck gamma v t2 ct blockchain) m;
        if compareType t_exp t2 ct then () else raise (TypeMismatch (t_exp, t2))
      | _ -> raise (TypeMismatch (Map(UInt, t_exp), t))
    end
  | Var _ -> axioms gamma e t ct
  (* subsittuir por infer_type gamma AritOp a ct ????? *)
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
  | Revert -> axioms gamma e t ct 
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
    axioms gamma e t ct  
  | MsgValue ->
    axioms gamma e t ct  
  | If (e1, e2, e3) -> 
    typecheck gamma e1 Bool ct blockchain;
    typecheck gamma e2 t ct blockchain;
    typecheck gamma e3 t ct blockchain;
  | Assign (s, e1) -> 
    typecheck gamma (Var s) t ct blockchain;
    typecheck gamma e1 t ct blockchain
  | This None -> 
    (*VER*)
    (* Verify if This references a contract *)
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars "this" in
        if compareType t_x t ct then () 
        else raise (TypeMismatch (t_x, t))
      with Not_found -> raise (UnboundVariable "this")
    end 
  | This Some (_s, _le) -> assert false
  (* how do we know what type we are expect blockchaining for our map? what are the values for t1 and t2? *)
  | MapRead (e1, e2) ->  
    begin match e1 with 
      | Val(VMapping (_, t_exp)) ->
        (* how do we know t1? *)
        typecheck gamma e1 (Map (UInt , t)) ct blockchain;
        typecheck gamma e2 UInt ct blockchain;
        if compareType t_exp t ct then () 
        else raise (TypeMismatch (t_exp, t))
      | _ -> raise (TypeMismatch (t, t))
    end
  | MapWrite (e1, e2, e3) ->
    begin match t with 
      | Map(t1, t2) ->
        typecheck gamma e1 t ct blockchain;
        typecheck gamma e2 t1 ct blockchain;
        typecheck gamma e3 t2 ct blockchain;
      | _ -> raise (TypeMismatch (Map(UInt, t), t))
    end
  | StateRead (e1, s) -> (*VER*)
    begin 
      typecheck gamma e1 CTop ct blockchain;
      let t_e : t_exp = infer_type gamma e1 ct in  
      let cname : string = match t_e with 
        | C name -> name 
        | Address (C name) -> name 
        | _ -> assert false 
      in
      let sv : (t_exp * string) list = state_vars_contract cname ct in 
      try
        let (t_e, _s) = List.find (fun (_, e_s) -> e_s = s) sv in 
        if compareType t_e t ct then () else raise (TypeMismatch (t_e, t))
      with Not_found -> raise (UnboundVariable "s")
    end
  | StateAssign (e1, s, e2) -> 
    typecheck gamma (StateRead (e1, s)) t ct blockchain;
    typecheck gamma e2 t ct blockchain;
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
    let (gamma_vars, _, _) = gamma in 
    typecheck gamma e1 t_e ct blockchain;
    Hashtbl.add gamma_vars s t_e;
    typecheck gamma e2 t ct blockchain;
  | _ -> assert false




(* type ty =
   | Mapping of ty * ty

   type context = (string * ty) list

   let rec infer_type (ctx : context) (exp : exp) : ty =
   match exp with
   | MappingAccess (e1, e2) ->
   let t1 = infer_type ctx e1 in
   let t2 = infer_type ctx e2 in
   begin match t1 with
    | Mapping (t3, t4) ->
      if subtype t2 t3 then t4
      else failwith "Type error: invalid mapping access"
    | _ -> failwith "Type error: expected a mapping"
   end
   (* Other cases for the infer_type function *)
   | _ -> failwith "Type error: unsupported expression"
   and subtype (t1 : ty) (t2 : ty) : bool =
   match t1, t2 with
   | Mapping (t11, t12), Mapping (t21, t22) ->
   subtype t21 t11 && subtype t12 t22
   | _, _ -> t1 = t2 *)
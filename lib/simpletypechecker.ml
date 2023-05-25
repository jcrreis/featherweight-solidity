open Types 
(* open C3  *)
(* open Utils *)
open Pprinters 


let axioms (gamma: gamma) (e: expr) : (t_exp, string) result = match e with 
  | Val (VBool _) -> Ok(Bool)  
  | Val (VUInt n) -> if n >= 0 then Ok(UInt) else Error("Invalid integer")
  | Revert -> Ok(TRevert)
  | Val (VUnit) -> Ok(Unit)
  | Val (VAddress a) -> 
    begin 
      try 
        (* gamma_vars * gamma_addresses * gamma_contracts *)
        let (_, gamma_addresses, _) = gamma in 
        let a = Hashtbl.find gamma_addresses (VAddress a) in 
        Ok(a)
        (* if subtyping a t ct then () else raise (TypeMismatch (a, t)) *)
      with Not_found -> raise (UnboundVariable a)
    end
  | Val (VContract i) ->
    begin 
      try 
        let (_, _, gamma_contracts) = gamma in 
        let c = Hashtbl.find gamma_contracts (VContract i) in 
        Ok(c)
        (* if subtyping c t ct then () else raise (TypeMismatch (c, t)) *)
      with Not_found -> raise (UnboundVariable "")
    end 
  | MsgSender -> 
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars "msg.sender" in
        Ok(t_x)
        (* if subtyping t_x t ct then () else raise (TypeMismatch (t_x, t)) *)
      with Not_found -> raise (UnboundVariable "msg.sender")
    end 
  | MsgValue -> Ok(UInt)
  | Var x -> 
    begin 
      try 
        Format.eprintf "\n%s" x;
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars x in
        Ok(t_x)
        (* Format.eprintf "%s ----> %s" (t_exp_to_string t_x) (t_exp_to_string t); *)
        (* if subtyping t_x t ct then () else raise (TypeMismatch (t_x, t)) *)
      with Not_found -> raise (UnboundVariable x)
    end 
  | _ -> assert false


let rec infer_type (gamma: gamma) (e: expr) (ct: contract_table) : (t_exp, string) result = 
  let type_infer_error t_exp : string = "Couldn't infer type " ^ (t_exp_to_string t_exp) in 
  let check_if_operands_uint (e1: expr) (e2: expr) (gamma: gamma) (ct: contract_table) : bool =
    let t_e1 = infer_type gamma e1 ct in 
    let t_e2 = infer_type gamma e2 ct in 
    match t_e1, t_e2 with 
      | Ok(t_e1), Ok(t_e2) -> if t_e1 = UInt && t_e2 = UInt then true else false 
      | _-> false 
  in 
  let check_if_operands_bool (e1: expr) (e2: expr) (gamma: gamma) (ct: contract_table) : bool =
    let t_e1 = infer_type gamma e1 ct in 
    let t_e2 = infer_type gamma e2 ct in 
    match t_e1, t_e2 with 
      | Ok(t_e1), Ok(t_e2) -> if t_e1 = Bool && t_e2 = Bool then true else false 
      | _-> false 
  in
  let infer_arit (gamma: gamma) (a: arit_ops) (ct: contract_table) : (t_exp, string) result = match a with 
    | Plus (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Div (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Times (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Minus (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Exp (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
    | Mod (e1, e2) -> 
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(UInt)
      else 
        Error(type_infer_error UInt)
  in
  let infer_bool (gamma: gamma) (b: bool_ops) (ct: contract_table) : (t_exp, string) result = match b with 
    | Neg e1 -> 
      let t_e1 = infer_type gamma e1 ct in 
      t_e1
    | Conj (e1, e2) -> 
      if check_if_operands_bool e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Disj (e1, e2) ->
      if check_if_operands_bool e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Equals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)

      (* if t <> Bool then 
        raise (TypeMismatch (Bool, t));
      begin 
        try 
          typecheck gamma e1 UInt ct blockchain;
          typecheck gamma e2 UInt ct blockchain
        with TypeMismatch _ -> 
          begin 
            typecheck gamma e1 (Address None) ct blockchain;
            typecheck gamma e2 (Address None) ct blockchain
          end 
      end *)
    | Greater (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | GreaterOrEquals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Lesser (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | LesserOrEquals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    | Inequals (e1, e2) ->
      if check_if_operands_uint e1 e2 gamma ct then 
        Ok(Bool)
      else 
        Error(type_infer_error Bool)
    in 
  match e with
  | Val _ -> axioms gamma e  
  | AritOp a -> infer_arit gamma a ct 
  | BoolOp b -> infer_bool gamma b ct 
  | Revert -> axioms gamma e 
  | Balance e1 -> 
    let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with 
      | Ok(Address _) -> Ok(UInt)
      | Ok(C _) -> Ok(UInt)
      | _ -> Error(type_infer_error (Address None))
    end
  | Address e1 -> 
    let t_e1 = infer_type gamma e1 ct in 
    begin
    match t_e1 with 
      | Ok(CTop) -> Ok(Address (Some(CTop)))
      | Ok(C i) -> Ok(Address (Some((C i))))
      | Ok(Address _) -> Ok(Address None)
      | _ -> Error(type_infer_error (Address None))
    end
  | Return e1 -> 
    let t_e1 = infer_type gamma e1 ct in
    t_e1
  | Seq (_, e2) ->
    (* inferencia *)
    let t_e2 = infer_type gamma e2 ct in 
    t_e2
  | MsgSender -> 
    axioms gamma e  
  | MsgValue ->
    axioms gamma e  
  | If (e1, e2, e3) ->
    begin 
      let t_e1 = infer_type gamma e1 ct in 
      if t_e1 <> Ok(Bool) then 
        Error("Malformed If expression")
      else
        let t_e2 = infer_type gamma e2 ct in 
        let t_e3 = infer_type gamma e3 ct in 
        if t_e2 = t_e3 then t_e2 else Error("Malformed If expression")
    end
  | Assign (s, e1) -> 
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_s = Hashtbl.find gamma_vars s in
        let t_e1 = infer_type gamma e1 ct in 
        if Ok(t_s) = t_e1 then Ok(Unit) else Error("Malformed Assign")
      with Not_found -> raise (UnboundVariable "this")
    end 
  | This None -> 
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars "this" in
        Ok(t_x)
      with Not_found -> raise (UnboundVariable "this")
    end 
  (* | This Some (s, le) ->
    let (gamma_vars, _, _) = gamma in 
    let t_this = Hashtbl.find gamma_vars "this" in 
    begin match t_this with 
      | C name -> begin 
        let ftype = function_type name s ct in 
        let (t_es, rettype) = ftype in 
        (* if subtyping t rettype ct then 
          List.iter2 (fun t_e e' -> typecheck gamma e' t_e ct blockchain;) t_es le
        else 
          raise (TypeMismatch (rettype, t)) *)
      end
      | _ -> raise (TypeMismatch (t_this, CTop))
    end *)
    (* | MapRead (e1, e2) ->  
      let typecheck_mapread e2 gamma t_x t ct blockchain = 
        match t_x with 
        | Map (t1, t2) -> 
          typecheck gamma e2 t1 ct blockchain;
          if subtyping t t2 ct then 
            ()
          else 
            raise (TypeMismatch (t, t2))
        | _ -> raise (Failure "unexpected operation")
      in
      begin match e1 with 
        | Var s ->
          begin 
            try 
            (* fazer função !*)
              let (gamma_vars, _, _) = gamma in 
              let t_x = Hashtbl.find gamma_vars s in
              typecheck_mapread e2 gamma t_x t ct blockchain
            with Not_found -> raise (UnboundVariable s)
          end
        | StateRead(e1, s) -> 
          typecheck gamma e1 CTop ct blockchain;
          begin 
            try 
              let (gamma_vars, _, _) = gamma in 
              let t_x = Hashtbl.find gamma_vars s in
              typecheck_mapread e2 gamma t_x t ct blockchain
            with Not_found -> raise (UnboundVariable s)
          end
        | _ ->  raise (Failure "unexpected operation")
      end
    | MapWrite (e1, e2, e3) ->
      Format.eprintf "%s" (t_exp_to_string t);
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
        typecheck gamma (Var s) t ct blockchain; 
      end
    | StateAssign (e1, s, e2) ->
      if t <> Unit then 
        raise (TypeMismatch (Unit, t));
      typecheck gamma e1 CTop ct blockchain;
      begin 
        try 
          let (gamma_vars, _, _) = gamma in 
          let t_x = Hashtbl.find gamma_vars s in
          typecheck gamma e2 t_x ct blockchain
        with Not_found -> raise (UnboundVariable s)
      end
    | Transfer (e1, e2) ->
      (* ver this gamma : c, porque está na regra*)
      if t <> Unit then 
        raise (TypeMismatch (Unit, t));
      typecheck gamma e2 UInt ct blockchain;
      typecheck gamma e1 (Address (Some CTop)) ct blockchain
    | New (s, e, le) ->
      (* type check contract blockchain ...*)
      if t <> (CTop) then 
        raise (TypeMismatch (CTop, t));
      typecheck gamma e UInt ct blockchain;
      let c_def: contract_def = Hashtbl.find ct s in
      let (args, _) = c_def.constructor in 
      let ts = List.map (fun (t_e, _) -> t_e) args in
      List.iter2 (fun t_cx e_cx -> typecheck gamma e_cx t_cx ct blockchain ) ts le;
    | Cons (s, e1) -> 
        (* typecheck gamma e1 (Address (Some (CTop))) ct blockchain; *)
        typecheck gamma e1 (Address (Some(C s))) ct blockchain;
    | CallTopLevel (e1, _s, e2, e3, _le) -> 
        begin
          typecheck gamma e1 CTop ct blockchain;
          typecheck gamma e2 UInt ct blockchain;
          typecheck gamma e3 (Address None) ct blockchain; 
          match e1 with 
            | This None -> ()
            | Cons (_s, _e1) -> ()
            | _ -> assert false 
          end
    | Call (e1, _s, e2, _le) -> 
      (*TODO*)
      begin
        typecheck gamma e1 CTop ct blockchain;
        typecheck gamma e2 UInt ct blockchain;
        match e1 with 
            | This None -> ()
            | Cons (_s, _e1) -> ()
            | New (_s, _e, _le) -> ()
            | _ -> assert false 
      end
    | Let (t_e, s, e1, e2) -> 
      let (gamma_vars, _, _) = gamma in 
      typecheck gamma e1 t_e ct blockchain;
      Hashtbl.add gamma_vars s t_e;
      typecheck gamma e2 t ct blockchain
    | AddContract _ -> assert false *)
  | _ -> assert false

let rec typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) : unit = 
  let typecheck_axioms (gamma: gamma) (e: expr) (t: t_exp) : unit = 
    let t_e = axioms gamma e in 
      begin match t_e with 
        | Ok(t_e) -> if t_e = t then () else raise (TypeMismatch (t_e, t))
        | Error(s) -> raise (Failure s)
      end
  in 
  let typecheck_arit_op (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table): unit =
    match e with 
      | AritOp a -> 
        begin match a with 
          | Plus (e1, e2) -> 
            if t <> UInt then 
              raise (TypeMismatch (UInt, t));
            typecheck gamma e1 UInt ct;
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
      | _ -> assert false 
    
  in
  let typecheck_bool_op (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table): unit =
    match e with 
      | BoolOp b -> 
        begin match b with 
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
            begin 
              try 
                typecheck gamma e1 UInt ct;
                typecheck gamma e2 UInt ct
              with TypeMismatch _ -> 
                begin 
                  typecheck gamma e1 (Address None) ct;
                  typecheck gamma e2 (Address None) ct
                end 
            end
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
      | _ -> assert false 
      
  in
  match e with 
    | Val _ -> typecheck_axioms gamma e t 
    | Var _ -> typecheck_axioms gamma e t 
    | Revert -> typecheck_axioms gamma e t 
    | MsgSender -> typecheck_axioms gamma e t  
    | MsgValue -> typecheck_axioms gamma e t 
    | AritOp _ -> typecheck_arit_op gamma e t ct
    | BoolOp _ -> typecheck_bool_op gamma e t ct 
    
    (* | Val (VMapping (m, t_exp)) -> 
      begin match t with 
        | Map (t1, t2) -> 
          (* C name ; Address name*)
          Hashtbl.iter (fun k v -> 
            typecheck gamma k t1 ct blockchain; 
                        typecheck gamma v t2 ct blockchain) m;
          if subtyping t_exp t2 ct then () else raise (TypeMismatch (t_exp, t2))
        | _ -> raise (TypeMismatch (Map(UInt, t_exp), t))
      end *)
    
    (* subsittuir por infer_type gamma AritOp a ct ????? *)
    (* | AritOp a -> begin match a with 
        | Plus (e1, e2) -> 
          if t <> UInt then 
            raise (TypeMismatch (UInt, t));
          typecheck gamma e1 UInt ct blockchain;
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
          begin 
            try 
              typecheck gamma e1 UInt ct blockchain;
              typecheck gamma e2 UInt ct blockchain
            with TypeMismatch _ -> 
              begin 
                typecheck gamma e1 (Address None) ct blockchain;
                typecheck gamma e2 (Address None) ct blockchain
              end 
          end
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
    
    | Balance e1 -> 
      if t <> UInt then 
        raise (TypeMismatch (UInt, t));
      typecheck gamma e1 (Address (Some CTop)) ct blockchain;
    | Address e1 -> 
      begin match t with 
        | Address (Some CTop) -> typecheck gamma e1 CTop ct blockchain
        | Address (Some (C i)) -> typecheck gamma e1 (C i) ct blockchain
        | _ -> raise (TypeMismatch (Address (Some CTop), t))
      end 
    | Return e1 -> typecheck gamma e1 t ct blockchain 
    | Seq (e1, e2) ->
      (* inferencia *)
      typecheck gamma e1 Unit ct blockchain;
      typecheck gamma e2 t ct blockchain
      
    | If (e1, e2, e3) -> 
      typecheck gamma e1 Bool ct blockchain;
      typecheck gamma e2 t ct blockchain;
      typecheck gamma e3 t ct blockchain; *)
    | _ -> assert false
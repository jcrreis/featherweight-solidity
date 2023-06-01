open Types 
open C3 
open Utils
open Pprinters 


let rec _subtyping (t1: t_exp) (t2: t_exp) (ct: contract_table) : bool = 
  match t1, t2 with 
  | CTop, CTop -> true
  | CTop, C _ -> false 
  | C _, CTop -> true
  | C name1, C name2 -> 
    let contract_def: contract_def = Hashtbl.find ct name1 in
    let contract_hierarchy: string list = match c3_linearization contract_def with 
      | Ok v -> v
      | _ -> assert false 
    in
    if List.mem name2 contract_hierarchy then true else false
  | Address (Some _), Address None -> true 
  | Address None, Address (Some _) -> false  
  | Address (Some _), Address (Some CTop) -> true 
  | Address (Some CTop), Address (Some _) -> false 
  | Address (Some c1), Address Some c2 -> _subtyping c1 c2 ct
  | _ -> t1 = t2

let ctypes name ct = 
  let c_def: contract_def = Hashtbl.find ct name in
  let (args, _) = c_def.constructor in 
  let ts = List.map (fun (t_e, _) -> t_e) args in
  ts

let get_var_type_from_gamma (s: string) (gamma: gamma) : t_exp = 
  try 
    let (gamma_vars, _, _) = gamma in 
    let t_x = Hashtbl.find gamma_vars s in
    t_x
  with Not_found -> raise (UnboundVariable s)

let axioms (gamma: gamma) (e: expr) : (t_exp, string) result = match e with 
  | Val (VBool _) -> Ok(Bool)  
  | Val (VUInt n) -> if n >= 0 then Ok(UInt) else Error("Invalid integer")
  | Revert -> Ok(TRevert)
  | Val (VUnit) -> Ok(Unit)
  | Val (VAddress a) -> 
    begin 
      try 
        let (_, gamma_addresses, _) = gamma in 
        let a = Hashtbl.find gamma_addresses (VAddress a) in 
        Ok(a)
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
    let t_e = get_var_type_from_gamma "msg.sender" gamma in 
    Ok(t_e)
  | MsgValue -> Ok(UInt)
  | Var x -> 
    let t_e = get_var_type_from_gamma x gamma in 
    Ok(t_e)
  | This None -> 
    let t_e = get_var_type_from_gamma "this" gamma in 
    Ok(t_e)
  | _ -> assert false


let rec infer_type (gamma: gamma) (e: expr) (ct: contract_table) : (t_exp, string) result = 
  let type_infer_error e : string = "Couldn't infer type of expr: " ^ (expr_to_string e) in 
  let infer_arit (gamma: gamma) (a: arit_ops) (ct: contract_table) : (t_exp, string) result = match a with 
    | Plus _ | Div _ | Times _ | Minus _ | Exp _ | Mod _ -> 
      try 
        typecheck gamma (AritOp(a)) UInt ct;
        Ok(UInt)
      with TypeMismatch _-> Error(type_infer_error e)
  in
  let infer_bool (gamma: gamma) (b: bool_ops) (ct: contract_table) : (t_exp, string) result = match b with 
    | Neg _ | Conj _ | Disj _ | Equals _ | Greater _ | GreaterOrEquals _ | Lesser _ | LesserOrEquals _ | Inequals _ -> 
      try 
        typecheck gamma (BoolOp(b)) Bool ct;
        Ok(Bool)
      with TypeMismatch _-> Error(type_infer_error e)
  in
  let verify_function_params t_es le rettype =  
    List.iter2 (fun t_e e' -> 
      let t_e' = infer_type gamma e' ct in
      match t_e' with 
        | Ok(t_e') -> if t_e <> t_e' then raise (TypeMismatch (t_e', t_e)) else ()
        | Error s -> raise (Failure s)
    ) t_es le;
    Ok(rettype)
  in
  match e with
  | Val _ | Var _ | Revert | This None | MsgSender | MsgValue -> axioms gamma e  
  | AritOp a -> infer_arit gamma a ct 
  | BoolOp b -> infer_bool gamma b ct 
  | Balance e1 -> 
    begin try
      typecheck gamma (Balance(e1)) UInt ct; 
      Ok(UInt)
    with TypeMismatch _ -> Error (type_infer_error (e))
    end
    (* let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with 
      | Ok(Address _) -> Ok(UInt)
      | Ok(C _) -> Ok(UInt)
      | _ -> Error(type_infer_error (e))
    end *)
  | Assign (s, e1) ->
    begin try 
      typecheck gamma (Assign(s, e1)) Unit ct;
      Ok(Unit)
    with TypeMismatch _ -> Error (type_infer_error (e))
    end
    (* let t_s =  get_var_type_from_gamma s gamma in  
    let t_e1 = infer_type gamma e1 ct in 
    if Ok(t_s) = t_e1 then Ok(Unit) else Error("Malformed Assign") *)
  | Address e1 -> 
    let t_e1 = infer_type gamma e1 ct in 
    begin
    match t_e1 with 
      | Ok(CTop) -> Ok(Address (Some(CTop)))
      | Ok(C i) -> Ok(Address (Some((C i))))
      | Ok(Address _) -> Ok(Address None)
      | _ -> Error(type_infer_error e)
    end
  | Return e1 -> 
    let t_e1 = infer_type gamma e1 ct in
    t_e1
  | Seq (e1, e2) ->
    begin try 
      let t_e2 = infer_type gamma e2 ct in 
      match t_e2 with 
        | Ok(t_e2) -> typecheck gamma (Seq(e1, e2)) t_e2 ct; Ok(t_e2)
        | Error s -> raise (Failure s)
    with TypeMismatch _ -> Error(type_infer_error e)
    end 
    (* let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with 
      | Ok _ ->  infer_type gamma e2 ct
      | Error s -> Error s
    end   *)
  | If (e1, e2, e3) ->
    begin 
      let t_e1 = infer_type gamma e1 ct in 
      if t_e1 <> Ok(Bool) then 
        Error("Malformed If expression: condition must be a bool")
      else
        let t_e2 = infer_type gamma e2 ct in 
        let t_e3 = infer_type gamma e3 ct in 
        match t_e2, t_e3 with 
          | Ok(t_e2), Ok(t_e3) -> if t_e2 = t_e3 then Ok(t_e2) else Error("Malformed If expression: it should return same type")
          | Error s, _ -> raise (Failure s)
          | _, Error s -> raise (Failure s)
    end
  | This Some (s, le) -> 
    let t_this = get_var_type_from_gamma "this" gamma in 
    begin match t_this with 
      | C name -> 
        begin 
          let ftype = function_type name s ct in 
          let (t_es, rettype) = ftype in 
          verify_function_params t_es le rettype
        end
      | _ -> Error ("Invalid type for this")
    end
    | MapRead (e1, e2) ->  
      let t_e1 = infer_type gamma e1 ct in 
      begin match t_e1 with 
        | Ok(Map(t1, rettype)) ->
          let t_e2 = infer_type gamma e2 ct in 
          begin match t_e2 with 
            | Ok(t2) -> if t2 = t1 then Ok(rettype) else Error ("Invalid operation")
            | Error s -> raise (Failure s)
          end
        | Error s -> raise (Failure s)
        | _ -> raise (Failure "Unexpected operation")
      end
    | MapWrite (e1, e2, e3) ->
      let t_e2 = infer_type gamma (MapRead(e1, e2)) ct in 
      let t_e3 = infer_type gamma e3 ct in 
      begin match t_e2, t_e3 with 
        | Ok(t2), Ok(t3) -> if t2 = t3 then infer_type gamma e1 ct else raise (Failure "Unexpected operation")
        | Error s, _ -> Format.eprintf "%s" s; raise (Failure s)
        | _, Error s -> Format.eprintf "%s" s; raise (Failure s)
      end
    | StateRead(e1, s) ->
      let t_e1 = infer_type gamma e1 ct in 
      begin match t_e1 with 
        | Ok(C _) -> Ok (get_var_type_from_gamma s gamma) (* can't allow C to be outside contract*)
        | Error s -> raise (Failure s)
        | _ -> raise (Failure "Unexpected operation")
      end
    | StateAssign (e1, s, e2) ->
      let t_s = infer_type gamma (StateRead(e1, s)) ct in 
      let t_e2 = infer_type gamma e2 ct in 
      if Ok(t_s) = Ok(t_e2) then Ok(Unit) else raise (Failure "Invalid operation") 
    | Transfer (e1, e2) ->
      let t_e1 = infer_type gamma e1 ct in 
      let t_e2 = infer_type gamma e2 ct in 
      if t_e1 = Ok(Address None) && t_e2 = Ok(UInt) then Ok(Unit) else raise (Failure "Invalid operation")
    | New (s, e1, le) ->
      (* type check contract blockchain ...*)
      let t_e1 = infer_type gamma e1 ct in 
      if t_e1 <> Ok(UInt) then raise (Failure "Invalid operation")
      else 
        let ts = ctypes s ct in 
        List.iter2 (fun t_e e' -> 
          let t_e' = infer_type gamma e' ct in
          match t_e' with 
            | Ok(t_e') -> if t_e <> t_e' then raise (TypeMismatch (t_e', t_e)) else ()
            | Error s -> raise (Failure s)
        ) ts le;
        Ok(C s)
    | Call (e1, s, e2, le) -> 
      begin
        let t_e2 = infer_type gamma e2 ct in 
        if t_e2 <> Ok(UInt) then raise (Failure "Invalid operation")
        else
          let t_e1 = infer_type gamma e1 ct in 
          begin match t_e1 with
            | Ok(C name) -> 
              begin 
                let ftype = function_type name s ct in 
                let (t_es, rettype) = ftype in 
                verify_function_params t_es le rettype
              end
            | Error s -> raise (Failure s)
            | _ -> raise (Failure "Invalid operation")
          end
      end
    | Cons(s, e1) -> 
      let t_e1 = infer_type gamma e1 ct in 
      begin match t_e1 with 
        | Ok(Address _) -> Ok(C s) 
        | Ok(_) -> raise (Failure "invalid type")
        | Error s -> raise (Failure s)
      end
    | _ -> (Format.eprintf "missing infer case for: %s" (expr_to_string e)) ;assert false

and typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) : unit = 
  let typecheck_axioms (gamma: gamma) (e: expr) (t: t_exp) : unit = 
    let t_e = axioms gamma e in 
      begin match t_e with 
        | Ok(t_e) -> 
          begin match t_e with 
            | TRevert -> () 
            | C _ -> if (t = CTop) || (t_e = t) then () else raise (TypeMismatch (t_e, t))
            | _ -> if t_e = t then () else raise (TypeMismatch (t_e, t))
          end
        | Error(s) -> raise (Failure s)
      end
  in 
  let typecheck_arit_op (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table): unit =
    match e with 
      | AritOp a -> 
        begin match a with 
          | Plus (e1, e2) | Div (e1, e2) | Times (e1, e2) | Minus (e1, e2) | Exp (e1, e2) | Mod (e1, e2)-> 
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
          | Conj (e1, e2) | Disj (e1, e2)-> 
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
          | Greater (e1, e2) | GreaterOrEquals (e1, e2) | Lesser (e1, e2) | LesserOrEquals (e1, e2) | Inequals (e1, e2)->
            if t <> Bool then 
              raise (TypeMismatch (Bool, t));
            typecheck gamma e1 UInt ct;
            typecheck gamma e2 UInt ct
        end
      | _ -> assert false 
      
  in
  let fun_check cname fun_name le ct t = 
    let ftype = function_type cname fun_name ct in 
    let (t_es, rettype) = ftype in 
    if t = rettype then 
      List.iter2 (fun t_e e' -> typecheck gamma e' t_e ct;) t_es le
    else 
      raise (TypeMismatch (rettype, t))
  in
  match e with 
    | Val (VMapping (m, t_exp)) -> 
      begin match t with 
        | Map (t1, t2) -> 
          Hashtbl.iter (fun k v -> 
            typecheck gamma k t1 ct; 
                        typecheck gamma v t2 ct) m;
          if t_exp = t2 then () else raise (TypeMismatch (t_exp, t2))
        | _ -> raise (TypeMismatch (Map(UInt, t_exp), t))
      end
    | Val _  | MsgValue | Var _ | MsgSender | Revert | This None -> typecheck_axioms gamma e t 
    | AritOp _ -> typecheck_arit_op gamma e t ct
    | BoolOp _ -> typecheck_bool_op gamma e t ct 
    | Balance e1 -> 
      if t <> UInt then raise (TypeMismatch (UInt, t));
      typecheck gamma e1 (Address (Some CTop)) ct
    | Return e1 -> 
      Format.eprintf "\n%s ----> %s\n" (t_exp_to_string t) (expr_to_string e1);
      typecheck gamma e1 t ct 
    | Seq (e1, e2) -> 
      let t_e1 = infer_type gamma e1 ct in 
      begin match t_e1 with 
        | Ok(t_e1) -> typecheck gamma e1 t_e1 ct; typecheck gamma e2 t ct
        | Error s -> raise (Failure s)
      end
    | Let(t_e, s, e1, e2) -> 
      let (gamma_vars, _, _) = gamma in 
      typecheck gamma e1 t_e ct;
      Hashtbl.add gamma_vars s t_e;
      typecheck gamma e2 t ct
    | If (e1, e2, e3) -> 
      typecheck gamma e1 Bool ct;
      typecheck gamma e2 t ct;
      typecheck gamma e3 t ct
    | Assign (s, e1) -> 
      Format.eprintf "%s" (t_exp_to_string t);
      if t <> Unit then 
        raise (TypeMismatch (Unit, t));
      let t_e1 = infer_type gamma e1 ct in 
      begin match t_e1 with 
        | Ok(t_e1) -> typecheck gamma (Var s) t_e1 ct;
        | Error s -> raise (Failure s)
      end
    | Transfer (e1, e2) ->
      if t <> Unit then 
        raise (TypeMismatch (Unit, t));
      typecheck gamma e1 (Address None) ct;
      typecheck gamma e2 UInt ct
    | StateAssign(e1, s, e2) -> 
      if t <> Unit then 
        raise (TypeMismatch (Unit, t));
      typecheck gamma e1 CTop ct;
      let t_s = get_var_type_from_gamma s gamma in 
      typecheck gamma e2 t_s ct
    | MapWrite(e1, e2, e3) -> 
      begin match t with 
        | Map(t1, t2) ->
          typecheck gamma e1 t ct;
          typecheck gamma e2 t1 ct;
          typecheck gamma e3 t2 ct
        | _ -> raise (TypeMismatch (t, Map(TRevert, TRevert)))
      end
    | MapRead(e1, e2) -> 
      let t_e1 = infer_type gamma e1 ct in 
      begin match t_e1 with 
        | Ok(Map(t1, t2)) -> 
          if t2 <> t then 
            raise (TypeMismatch (t, t2));
          typecheck gamma e2 t1 ct;
        | Ok(t1) -> raise (TypeMismatch (t1, Map(TRevert, TRevert)))
        | Error s -> raise (Failure s)
      end
    | New (s, e1, le) ->
      if t <> (C s) then raise (TypeMismatch (C s, t))
      else
        typecheck gamma e1 UInt ct;
        let ts = ctypes s ct in 
        List.iter2 (fun t_e e' -> typecheck gamma e' t_e ct) ts le;
    | Cons (s, e1) -> 
      if t <> (C s) then raise (TypeMismatch (C s, t)) 
      else 
        typecheck gamma e1 (Address (Some (C s))) ct;
    | CallTopLevel (e1, s, e2, e3, le) -> 
      begin
        let t_e1 = infer_type gamma e1 ct in  
        match t_e1 with 
          | Ok(C name) -> 
            typecheck gamma e3 (Address None) ct;
            typecheck gamma e2 UInt ct;
            fun_check name s le ct t;
          | Ok(CTop) -> raise (Failure "Can't reference a top class")
          | Ok(t_e1) -> raise (TypeMismatch (t_e1, CTop))
          | Error s -> raise (Failure s) 
      end
    | Call (e1, s, e2, le) -> 
      begin
        let t_e1 = infer_type gamma e1 ct in  
        match t_e1 with 
          | Ok(C name) -> 
            typecheck gamma e2 UInt ct;
            fun_check name s le ct t;
          | Ok(CTop) -> raise (Failure "Can't reference a top class")
          | Ok(t_e1) -> raise (TypeMismatch (t_e1, CTop))
          | Error s -> raise (Failure s) 
      end
    | This Some(s, le) -> 
      let (gamma_vars, _, _) = gamma in 
      let t_this = Hashtbl.find gamma_vars "this" in 
      begin match t_this with 
        | C name -> fun_check name s le ct t;
        | _ -> raise (TypeMismatch (t_this, CTop))
      end
    | StateRead(e1, s) -> 
      typecheck gamma e1 CTop ct;
      let t_s = get_var_type_from_gamma s gamma in
      if t_s = t then () else raise (TypeMismatch (t_s, t))
    | Address e1 -> 
      if t <> (Address (Some CTop)) then 
        raise (TypeMismatch (Address (Some CTop), t))
      else
        let t_e1 = infer_type gamma e1 ct in 
        begin match t_e1 with 
          | Ok(C _) -> ()
          | Ok(CTop) -> ()
          | Ok(t_e1) -> raise (TypeMismatch (t_e1, CTop))
          | Error s -> raise (Failure s)
        end
    | _ -> assert false

let typecheck_contract (g: gamma) (c: contract_def) (ct: contract_table) : unit = 
  let typecheck_constructor (g: gamma) (constructor: (t_exp * string) list * expr) (ct: contract_table): unit = 
    let (gv, ga, gc) = g in
    let (args, body) = constructor in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (args);
    typecheck (gv, ga, gc) body Unit ct; 
  in 
  let typecheck_function (g: gamma) (f: fun_def) (ct: contract_table): unit =
    let (gv, ga, gc) = g in 
    let rettype: t_exp = f.rettype in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (f.args);
    typecheck (gv, ga, gc) (f.body) rettype ct;
  in 
  let (gv, ga, gc) = g in 
  Hashtbl.add gv "this" (C c.name);
  Hashtbl.add gv "msg.sender" (Address None);
  Hashtbl.add gv "msg.value" (UInt);
  List.iter (fun (t_e, s) -> Format.eprintf "%s ---> %s" s (t_exp_to_string t_e); Hashtbl.add gv s t_e;) (c.state);
  typecheck_constructor (gv, ga, gc) c.constructor ct;     
  List.iter (fun (f_def: fun_def) -> typecheck_function (gv, ga, gc) f_def ct) (c.functions);
  Format.eprintf "\nContrato Validado com Sucesso!!\n"
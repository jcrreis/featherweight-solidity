open Types 
open C3 
open Utils
open Pprinters 


let issc (t1: t_exp) (t2: t_exp) (ct: contract_table) : bool =
  t2 = CTop ||   
  (
    match t1, t2 with 
    | C name1, C name2 -> let contract_def: contract_def = Hashtbl.find ct name1 in
      let contract_hierarchy: string list = match c3_linearization contract_def with 
        | Ok v -> v
        | Error s -> raise (Failure s)
      in
      (List.mem name2 contract_hierarchy)
    | _ -> raise (Failure "unexpected values!")
  )


let rec subtyping (t1: t_exp) (t2: t_exp) (ct: contract_table) : bool = 
  match t1, t2 with
  | CTop, CTop | C _, CTop | C _, C _ -> issc t1 t2 ct 
  (* | CTop, C _ -> false  *)
  | Address (Some _), Address None -> true 
  (* | Address None,  Address (Some _) -> false  *)
  | Address (Some t1), Address (Some t2) ->  subtyping t1 t2 ct 
  | _ -> t1 = t2


let ctypes name ct = 
  let c_def: contract_def = Hashtbl.find ct name in
  let (args, _) = c_def.constructor in 
  let ts = List.map (fun (t_e, _) -> t_e) args in
  ts

let get_var_type_from_gamma (s: string) (gamma: gamma) : t_exp = 
  try 
    let (gamma_vars, _,  _, _) = gamma in 
    let t_x = Hashtbl.find gamma_vars s in
    t_x
  with Not_found -> raise (UnboundVariable s)

let get_state_var_type_from_gamma (s: string) (gamma: gamma) : t_exp = 
  try 
    let (_, gamma_sv, _, _) = gamma in 
    let t_x = Hashtbl.find gamma_sv s in
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
        let (_, _, gamma_addresses, _) = gamma in 
        let a = Hashtbl.find gamma_addresses (VAddress a) in 
        Ok(a)
      with Not_found -> raise (UnboundVariable a)
    end
  | Val (VContract i) ->
    begin 
      try 
        let (_, _, _, gamma_contracts) = gamma in 
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
      typecheck gamma (AritOp(a)) UInt ct;
      Ok(UInt)
  in
  let infer_bool (gamma: gamma) (b: bool_ops) (ct: contract_table) : (t_exp, string) result = match b with 
    | Neg _ | Conj _ | Disj _ | Equals _ | Greater _ | GreaterOrEquals _ | Lesser _ | LesserOrEquals _ | Inequals _ -> 
      typecheck gamma (BoolOp(b)) Bool ct;
      Ok(Bool)
  in
  match e with
  | Val _ | Var _ | Revert | This None | MsgSender | MsgValue -> axioms gamma e  
  | AritOp a -> infer_arit gamma a ct 
  | BoolOp b -> infer_bool gamma b ct 
  | Balance e1 -> 
    typecheck gamma (Balance(e1)) UInt ct; 
    Ok(UInt)
  | Assign (s, e1) ->
    typecheck gamma (Assign(s, e1)) Unit ct;
    Ok(Unit)
  | Address e1 -> 
    typecheck gamma (Address e1) (Address None) ct;
    Ok(Address None)
  | Return e1 ->
    (* typecheck ??*) 
    let t_e1 = infer_type gamma e1 ct in
    t_e1
  | Seq (e1, e2) ->
    begin try 
        let t_e2 = infer_type gamma e2 ct in 
        match t_e2 with 
        | Ok(t_e2) -> typecheck gamma (Seq(e1, e2)) t_e2 ct; Ok(t_e2)
        | Error s -> Error s
      with TypeMismatch _ -> Error(type_infer_error e)
    end 
  | If (e1, e2, e3) ->
    begin 
      typecheck gamma e1 Bool ct;
      let t_e2 = infer_type gamma e2 ct in 
      match t_e2 with 
      | Ok(t_e2) -> typecheck gamma e3 t_e2 ct; Ok(t_e2)
      | Error s -> Error s
    end
  | This Some (s, le) -> 
    let t_this = get_var_type_from_gamma "this" gamma in 
    begin match t_this with 
      | C name -> 
        begin 
          let ftype = function_type name s ct in 
          let (_, rettype) = ftype in 
          typecheck gamma (This (Some (s, le))) rettype ct;
          Ok(rettype)
        end
      | _ -> Error ("Invalid type for this: this can only reference its contract!")
    end
  | MapRead (e1, e2) ->  
    let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with 
      | Ok(Map(_, rettype)) ->
        typecheck gamma (MapRead (e1, e2)) rettype ct;
        Ok(rettype)
      | Error s -> Error s
      | Ok(t_e1) -> Error ("Expected a mapping(a' => b') type instead of " ^ (t_exp_to_string t_e1))
    end
  | MapWrite (e1, e2, e3) ->
    let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with 
      | Ok(t_e1) -> typecheck gamma (MapWrite (e1, e2, e3)) t_e1 ct; Ok(t_e1)
      | Error s -> Error s
    end
  | StateRead(e1, s) ->
    let t_s = get_state_var_type_from_gamma s gamma in
    typecheck gamma (StateRead(e1, s)) t_s ct;
    Ok(t_s)
  | StateAssign (e1, s, e2) ->
    let t_s = get_state_var_type_from_gamma s gamma in
    typecheck gamma (StateAssign (e1, s, e2)) Unit ct;
    Ok(t_s)
  | Transfer (e1, e2) ->
    typecheck gamma (Transfer (e1, e2)) Unit ct;
    Ok(Unit)
  | New (s, e1, le) ->
    typecheck gamma (New (s, e1, le)) (C s) ct;
    Ok(C s)
  | Call (e1, s, e2, le) -> 
    typecheck gamma e2 UInt ct;
    let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with
      | Ok(C name) -> 
        begin 
          let ftype = function_type name s ct in 
          let (_, rettype) = ftype in 
          typecheck gamma (Call (e1, s, e2, le)) rettype ct;
          Ok(rettype)
        end
      | Error s -> Error s
      | Ok(t_e1) -> Error ("Expected contract reference instead of " ^ (t_exp_to_string t_e1))
    end
  | Cons(s, e1) -> 
    typecheck gamma (Cons (s, e1)) (C s) ct;
    Ok(C s)
  | _ -> (Format.eprintf "missing infer case for: %s" (expr_to_string e)) ;assert false

and typecheck (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table) : unit = 
  let typecheck_axioms (gamma: gamma) (e: expr) (t: t_exp) (ct: contract_table): unit = 
    let t_e = axioms gamma e in 
    begin match t_e with 
      | Ok(t_e) -> 
        begin match t_e with 
          | TRevert -> () 
          | _-> (if subtyping t_e t ct then () else raise (TypeMismatch (t_e, t)))
          (* | _ -> if t_e = t then () else raise (TypeMismatch (t_e, t)) *)
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
  let fun_check gamma cname fun_name le ct t = 
    let ftype = function_type cname fun_name ct in 
    let (t_es, rettype) = ftype in
    (* SUBTYPING NEEDED! *) 
    if subtyping rettype t ct then 
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
  | Val _  | MsgValue | Var _ | MsgSender | Revert | This None -> typecheck_axioms gamma e t ct
  | AritOp _ -> typecheck_arit_op gamma e t ct
  | BoolOp _ -> typecheck_bool_op gamma e t ct 
  | Balance e1 -> 
    if t <> UInt then raise (TypeMismatch (UInt, t));
    typecheck gamma e1 (Address None) ct
  | Return e1 -> 
    typecheck gamma e1 t ct 
  | Seq (e1, e2) -> 
    let t_e1 = infer_type gamma e1 ct in 
    begin match t_e1 with 
      | Ok(_) -> typecheck gamma e2 t ct
      | Error s -> raise (Failure s)
    end
  | Let(t_e, s, e1, e2) -> 
    let (gamma_vars, _, _, _) = gamma in 
    typecheck gamma e1 t_e ct;
    Hashtbl.add gamma_vars s t_e;
    typecheck gamma e2 t ct
  | If (e1, e2, e3) -> 
    typecheck gamma e1 Bool ct;
    typecheck gamma e2 t ct;
    typecheck gamma e3 t ct
  | Assign (s, e1) -> 
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
    let t_s = get_state_var_type_from_gamma s gamma in 
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
        if not (subtyping t2 t ct) then (* subtyping *)
          raise (TypeMismatch (t, t2));
        typecheck gamma e2 t1 ct;
      | Ok(t1) -> raise (TypeMismatch (t1, Map(TRevert, TRevert)))
      | Error s -> raise (Failure s)
    end
  | New (s, e1, le) ->
    if (not (subtyping (C s) t ct)) then raise (TypeMismatch (C s, t))
    else
      typecheck gamma e1 UInt ct;
    let ts = ctypes s ct in 
    List.iter2 (fun t_e e' -> typecheck gamma e' t_e ct) ts le;
  | Cons (s, e1) -> 
    if (not (subtyping (C s) t ct)) then raise (TypeMismatch (C s, t)) 
    else
      begin try 
          typecheck gamma e1 (C s) ct;
        with TypeMismatch _ -> typecheck gamma e1 (Address (Some (C s))) ct;
      end
  | CallTopLevel (e1, s, e2, e3, le) -> 
    begin
      let t_e1 = infer_type gamma e1 ct in  
      match t_e1 with 
      | Ok(C name) -> 
        typecheck gamma e3 (Address None) ct;
        typecheck gamma e2 UInt ct;
        fun_check gamma name s le ct t;
      | Ok(CTop) -> raise (Failure "Can't reference a top class")
      | Ok(t_e1) -> raise (TypeMismatch (t_e1, CTop))
      | Error s -> raise (Failure s) 
    end
  | Call (e1, s, e2, le) -> 
    begin
      let t_e1 = infer_type gamma e1 ct in
      match t_e1 with 
      | Ok(C name) ->
        let (gv, _, _, _) = gamma in 
        let t_sender = match fsender name s ct with 
          | Ok t_sender -> t_sender 
          | Error s -> raise (Failure s)
        in 
        Hashtbl.add gv "msg.sender" t_sender;
        typecheck gamma e2 UInt ct;
        fun_check gamma name s le ct t;
      | Ok(CTop) -> raise (Failure "Can't reference a top class")
      | Ok(t_e1) -> raise (TypeMismatch (t_e1, CTop))
      | Error s -> raise (Failure s) 
    end
  | This Some(s, le) -> 
    let (gamma_vars, _, _, _) = gamma in 
    let t_this = Hashtbl.find gamma_vars "this" in 
    begin match t_this with 
      | C name -> fun_check gamma name s le ct t;
      | _ -> raise (TypeMismatch (t_this, CTop))
    end
  | StateRead(e1, s) -> 
    typecheck gamma e1 CTop ct;
    let t_s = get_state_var_type_from_gamma s gamma in
    if subtyping t_s t ct then () else raise (TypeMismatch (t_s, t))
  | Address e1 -> 
    if t <> (Address None) then 
      raise (TypeMismatch (Address None, t))
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
    let (gv, gsv, ga, gc) = g in
    let (args, body) = constructor in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (args);
    typecheck (gv, gsv, ga, gc) body Unit ct; 
  in 
  let typecheck_function (g: gamma) (f: fun_def) (ct: contract_table): unit =
    let (gv, gsv, ga, gc) = g in 
    let rettype: t_exp = f.rettype in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (f.args);
    typecheck (gv, gsv, ga, gc) (f.body) rettype ct;
  in 
  Format.eprintf "%s" ("\nChecking contract: " ^ c.name ^ "\n");
  let (gv, gsv, ga, gc) = g in 
  Hashtbl.add gv "this" (C c.name);
  Hashtbl.add gv "msg.sender" (Address None);
  Hashtbl.add gv "msg.value" (UInt);
  List.iter (fun (t_e, s) -> Hashtbl.add gsv s t_e;) (c.state);
  typecheck_constructor (gv, gsv, ga, gc) c.constructor ct;     
  List.iter (fun (f_def: fun_def) -> typecheck_function (gv, gsv, ga, gc) f_def ct) (c.functions);
  Format.eprintf "\nContrato Validado com Sucesso!!\n"


open Types 
open Utils
open C3 
open Pprinters 


let rec subtyping (t1: t_exp) (t2: t_exp) (ct: contract_table) : bool = 
  match t1, t2 with 
  | Address _, Address (Some CTop) -> true
  | Address (Some CTop), Address _ -> false
  | Address (Some (C name1)), Address (Some (C name2)) -> 
    subtyping (C name1) (C name2) ct
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
        if subtyping a t ct then () else raise (TypeMismatch (a, t))
      with Not_found -> raise (UnboundVariable a)
    end
  | Val (VContract i), _ ->
    begin 
      try 
        let (_, _, gamma_contracts) = gamma in 
        let c = Hashtbl.find gamma_contracts (VContract i) in 
        if subtyping c t ct then () else raise (TypeMismatch (c, t))
      with Not_found -> raise (UnboundVariable "")
    end 
  | MsgSender, Address (Some CTop) -> ()
  | MsgSender, t -> 
    begin 
      try 
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars "msg.sender" in
        if subtyping t_x t ct then () else raise (TypeMismatch (t_x, t))
      with Not_found -> raise (UnboundVariable "msg.sender")
    end 
  | MsgValue, UInt -> ()
  | MsgValue, _ -> raise (TypeMismatch (UInt, t))
  | Var x, t -> 
    begin 
      try 
        Format.eprintf "\n%s" x;
        let (gamma_vars, _, _) = gamma in 
        let t_x = Hashtbl.find gamma_vars x in
        if subtyping t_x t ct then () else raise (TypeMismatch (t_x, t))
      with Not_found -> raise (UnboundVariable x)
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
        Hashtbl.iter (fun k v -> 
          typecheck gamma k t1 ct blockchain; 
                       typecheck gamma v t2 ct blockchain) m;
        if subtyping t_exp t2 ct then () else raise (TypeMismatch (t_exp, t2))
      | _ -> raise (TypeMismatch (Map(UInt, t_exp), t))
    end
  | Var _ -> axioms gamma e t ct
  (* subsittuir por infer_type gamma AritOp a ct ????? *)
  | AritOp a -> begin match a with 
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
  | Revert -> axioms gamma e t ct 
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
        if subtyping t_x t ct then () 
        else raise (TypeMismatch (t_x, t))
      with Not_found -> raise (UnboundVariable "this")
    end 
  | This Some (s, le) ->
    let (gamma_vars, _, _) = gamma in 
    let t_this = Hashtbl.find gamma_vars "this" in 
    begin match t_this with 
      | C name -> begin 
        let ftype = function_type name s ct in 
        let (t_es, rettype) = ftype in 
        Format.eprintf "%s ---> %s" (t_exp_to_string rettype) (t_exp_to_string t);
        if subtyping t rettype ct then 
          List.iter2 (fun t_e e' -> typecheck gamma e' t_e ct blockchain;) t_es le
        else 
          raise (TypeMismatch (rettype, t))
      end
      | _ -> raise (TypeMismatch (t_this, CTop))
    end
  | MapRead (e1, e2) ->  
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
  | Cons (_s, e1) -> 
    (* e1 is always an address, however it can be a Val (Address a) || MsgSender || Var x || this.sv *)
    (* we need to make sure that s == cname, thus we need to access the contract stored in the blockchain*)
    typecheck gamma e1 (Address (Some (CTop))) ct blockchain;
    (* get_contract_by_address blockchain a*)
    (* typecheck gamma e (C(-1)) ct blockchain *)
  | CallTopLevel (e1, _s, e2, e3, _le) -> 
      typecheck gamma e1 CTop ct blockchain;
      typecheck gamma e2 UInt ct blockchain;
      typecheck gamma e3 (Address None) ct blockchain; 
  | Let (t_e, s, e1, e2) -> 
    let (gamma_vars, _, _) = gamma in 
    typecheck gamma e1 t_e ct blockchain;
    Hashtbl.add gamma_vars s t_e;
    typecheck gamma e2 t ct blockchain;
  | _ -> assert false


let typecheck_contract (g: gamma) (c: contract_def) (ct: contract_table) (b: blockchain) : unit = 
  let typecheck_constructor (g: gamma) (constructor: (t_exp * string) list * expr) (ct: contract_table) (b: blockchain) : unit = 
    let (gv, ga, gc) = g in
    let (args, body) = constructor in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (args);
    typecheck (gv, ga, gc) body Unit ct b; 
  in 
  let typecheck_function (g: gamma) (f: fun_def) (ct: contract_table) (b: blockchain): unit =
    let (gv, ga, gc) = g in 
    let rettype: t_exp = f.rettype in 
    List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (f.args);
    (* Format.eprintf "%s" (expr_to_string f.body); *)
    typecheck (gv, ga, gc) (f.body) rettype ct b;
  in 
  let (gv, ga, gc) = g in 
  Hashtbl.add gv "this" (C c.name);
  Hashtbl.add gv "msg.sender" (Address None);
  Hashtbl.add gv "msg.value" (UInt);
  List.iter (fun (t_e, s) -> Hashtbl.add gv s t_e;) (c.state);
  typecheck_constructor (gv, ga, gc) c.constructor ct b;     
  List.iter (fun (f_def: fun_def) -> typecheck_function (gv, ga, gc) f_def ct b) (c.functions);
  Format.eprintf "\nContrato Validado com Sucesso!!\n"
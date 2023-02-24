open QCheck
open Featherweightsolidity 
open Fs 
open Types
open Pprinters

let _gen_string = 
  let ch = Gen.oneofl ['a'; 'b'; 'c'; 'd'] in
  Gen.string_of ch

let leafgen_type = Gen.oneofl[Bool; UInt; Address; Map (Address, UInt); Map (UInt, Address)]

let leafgen_int = Gen.oneof[ Gen.map (fun i -> Val(VUInt i)) Gen.int]

let leafgen_bool = Gen.oneof[ Gen.map (fun b -> if b then Val(VBool True) else Val(VBool False)) Gen.bool]

let rec gen_arit_op_ast n = match n with 
  | 0 -> leafgen_int
  | n -> Gen.oneof [
    leafgen_int;
    Gen.map2 (fun l r -> AritOp(Plus(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> AritOp(Div(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> AritOp(Times(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> AritOp(Minus(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> AritOp(Exp(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> AritOp(Mod(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));  
]


let rec gen_bool_op_ast n = match n with 
  | 0 -> leafgen_bool
  | n -> Gen.oneof [
    leafgen_bool;
    Gen.map (fun e -> BoolOp(Neg e)) (gen_bool_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(Conj(l,r))) (gen_bool_op_ast (n/2)) (gen_bool_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(Disj(l,r))) (gen_bool_op_ast (n/2)) (gen_bool_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(Equals(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(Greater(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(GreaterOrEquals(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(Lesser(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(Inequals(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
    Gen.map2 (fun l r -> BoolOp(LesserOrEquals(l,r))) (gen_arit_op_ast (n/2)) (gen_arit_op_ast (n/2));
]


                                                            
let _arb_type = make ~print:t_exp_to_string (leafgen_type)

(* let _gen_let_expr n = match n with  *)


let _gen_assign_expr (s: string) (e1: expr) : expr = Assign(s, e1)

let _gen_seq_expr (e1: expr) (e2: expr) : expr = Seq(e1, e2)

(* let rec _gen_expr_ast n = match n with 
  | 0 -> [
    leafgen_bool;
    leafgen_int;
  ]
  | _n -> Gen.oneof [
    leafgen_bool;
    leafgen_int;
    Gen.map2 (fun l r -> BoolOp(Conj(l,r))) (_gen_expr_ast (n/2)) (_gen_expr_ast (n/2));
] *)

let arb_tree_arit = make ~print:expr_to_string (gen_arit_op_ast 8)

let arb_tree_bool = make ~print:expr_to_string (gen_bool_op_ast 8)

(* let _gen_let_expr = Gen.oneof [ Gen.map (fun t_e s -> match t_e with 
  | _ -> Let(t_e, s, gen_string |> Gen.generate1 , gen_string |> Gen.generate1)
) leafgen_type gen_string] *)


let rec tshrink e = match e with 
  | Val(VUInt i) -> Iter.map (fun i' -> Val(VUInt i')) (Shrink.int i)
  | AritOp(Plus(l,r)) -> Iter.append 
    (Iter.map (fun l' -> AritOp(Plus(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> AritOp(Plus(l,r'))) (tshrink r))
  | AritOp(Div(l,r)) -> Iter.append 
    (Iter.map (fun l' -> AritOp(Div(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> AritOp(Div(l,r'))) (tshrink r))
  | AritOp(Times(l,r)) -> Iter.append 
    (Iter.map (fun l' -> AritOp(Times(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> AritOp(Times(l,r'))) (tshrink r))
  | AritOp(Minus(l,r)) -> Iter.append 
    (Iter.map (fun l' -> AritOp(Minus(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> AritOp(Minus(l,r'))) (tshrink r))
  | AritOp(Exp(l,r)) -> Iter.append 
    (Iter.map (fun l' -> AritOp(Exp(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> AritOp(Exp(l,r'))) (tshrink r))
  | AritOp(Mod(l,r)) -> Iter.append 
    (Iter.map (fun l' -> AritOp(Mod(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> AritOp(Mod(l,r'))) (tshrink r))
  | BoolOp(Neg e) -> Iter.map (fun e' -> BoolOp(Neg e')) (tshrink e)
  | BoolOp(Conj(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(Conj(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(Conj(l,r'))) (tshrink r))
  | BoolOp(Disj(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(Disj(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(Disj(l,r'))) (tshrink r))
  | BoolOp(Equals(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(Equals(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(Equals(l,r'))) (tshrink r))
  | BoolOp(Greater(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(Greater(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(Greater(l,r'))) (tshrink r))
  | BoolOp(GreaterOrEquals(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(GreaterOrEquals(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(GreaterOrEquals(l,r'))) (tshrink r))
  | BoolOp(Lesser(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(Lesser(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(Lesser(l,r'))) (tshrink r))
  | BoolOp(Inequals(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(Inequals(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(Inequals(l,r'))) (tshrink r))
  | BoolOp(LesserOrEquals(l,r)) -> Iter.append 
    (Iter.map (fun l' -> BoolOp(LesserOrEquals(l',r))) (tshrink l)) 
    (Iter.map (fun r' -> BoolOp(LesserOrEquals(l,r'))) (tshrink r))
  | _ -> Iter.empty



let test_contract = 
  let fb = {
    name = "fb";
    rettype = Unit;
    args = [];
    body = Return(Val(VUnit));
  } in  
  {
    name = "Test";
    state = [(Map(Address, UInt), "test_map"); (Address, "test_sv1"); (UInt, "test_sv2")];
    constructor = ([(Address, "test_sv1"); (UInt, "test_sv2")], Seq(
      (StateAssign(This None, "test_sv1", Var("test_sv1"))),
      (StateAssign(This None, "test_sv2", Var("test_sv2"))) 
    ));
    functions = [fb];
  }


let test_division_by_zero = Test.make ~name:"test division by zero"
  (set_shrink tshrink arb_tree_arit)
  (fun (e) -> 
    begin 
      let ct = Hashtbl.create 64 in 
      let vars = Hashtbl.create 64 in 
      let blockchain = Hashtbl.create 64 in  
      let sigma = Stack.create() in 
      (eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Div(e,Val (VUInt 0)))))
      =
      (blockchain, blockchain, sigma, Revert)
      )
      &&
      (eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Mod(e,Val (VUInt 0)))))
      =
      (blockchain, blockchain, sigma, Revert)
      )
    end
  ) 

let test_arit_plus_op = Test.make ~name:"test plus arithmetic operator"
  (set_shrink tshrink arb_tree_arit)
  (fun (e) -> 
    begin 
      let ct = Hashtbl.create 64 in 
      let vars = Hashtbl.create 64 in 
      let blockchain = Hashtbl.create 64 in  
      let sigma = Stack.create() in 
      let e' = AritOp(Plus(e,e)) in 

      (*Commutative 2e + e = e + 2e *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus(e',e))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus(e,e'))))
      ) 
        && 
      (*Associative e + (2e) + e = e + e + 2e *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus((AritOp(Plus(e,e'))), e))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus((AritOp(Plus(e,e))), e'))))
      )
        &&
      (* Identity property 0 + e = e *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus(Val(VUInt 0),e)))) 
        =
        eval_expr ct vars (blockchain, blockchain, sigma, e)
      )

    end
  )  

let test_arit_minus_op = Test.make ~name:"test minus arithmetic operator"
  (set_shrink tshrink arb_tree_arit)
  (fun (e) -> 
    begin 
      let ct = Hashtbl.create 64 in 
      let vars = Hashtbl.create 64 in 
      let blockchain = Hashtbl.create 64 in  
      let sigma = Stack.create() in 
      (* let e' = AritOp(Plus(e,e)) in  *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Minus(e,Val(VUInt 0))))) 
        =
        eval_expr ct vars (blockchain, blockchain, sigma, e)
      )
    end
)  

let test_arit_div_op = Test.make ~name:"test div arithmetic operator"
  (set_shrink tshrink arb_tree_arit)
  (fun (e) -> 
    begin 
      let ct = Hashtbl.create 64 in 
      let vars = Hashtbl.create 64 in 
      let blockchain = Hashtbl.create 64 in  
      let sigma = Stack.create() in 
      (* let e' = AritOp(Plus(e,e)) in  *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Div(e,Val(VUInt 1))))) 
        =
        eval_expr ct vars (blockchain, blockchain, sigma, e)
      )
    end
)  

let test_arit_times_op = Test.make ~name:"test times arithmetic operator"
  (set_shrink tshrink arb_tree_arit)
  (fun (e) -> 
    begin 
      let ct = Hashtbl.create 64 in 
      let vars = Hashtbl.create 64 in 
      let blockchain = Hashtbl.create 64 in  
      let sigma = Stack.create() in 
      let e' = AritOp(Plus(e,e)) in 
      (* Commutative 2e + e = e + 2e *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times(e',e))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times(e,e'))))
      ) 
        && 
      (* Associative e + (2e) + e = e + e + 2e *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times((AritOp(Times(e,e'))), e))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times((AritOp(Times(e,e))), e'))))
      )
        &&
      (*  *)
      (
        let (_, _, _, res) = 
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times(Val(VUInt 0),e)))) in 
        
        (res = Val(VUInt 0) || res = Revert)
      )
        && 
        (* Identity property 1 * e = e *)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times(Val(VUInt 1),e))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, e)
      )
    end
)  


let test_arit_op = Test.make ~name:"test arithmetic operators"
  (set_shrink tshrink arb_tree_arit)
  (fun (e) -> 
    begin 
      let ct = Hashtbl.create 64 in 
      let vars = Hashtbl.create 64 in 
      let blockchain = Hashtbl.create 64 in  
      let sigma = Stack.create() in 
      eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Plus(e,e))))
      =
      eval_expr ct vars (blockchain, blockchain, sigma, (AritOp(Times(Val(VUInt 2),e))))
    end
  )  
 (* Grupo Abeliano*)

let test_bool_op = Test.make ~name:"test boolean operators"
(set_shrink tshrink arb_tree_bool)
(fun (e) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    (
      (* De morgan laws*)
      (* https://www.google.com/search?q=algebra+de+boole&client=firefox-b-lm&source=lnms&tbm=isch&sa=X&ved=2ahUKEwiZi6OtkZX9AhXcXaQEHf_NCX0Q_AUoAXoECAEQAw&biw=1918&bih=924&dpr=1#imgrc=_SK3hsXB46ttzM*)
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Neg(BoolOp(Conj(e,e))))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Disj(BoolOp(Neg e), BoolOp(Neg e)))))
      )
      &&
      (
        eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Neg(BoolOp(Disj(e,e))))))
        =
        eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Conj(BoolOp(Neg e), BoolOp(Neg e)))))
      )
      &&
      (* elemento absorvente *)
      (
        let (_, _, _, res) = eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Conj(e,Val(VBool False))))) in 
        (res = Val(VBool False) || res = Revert)
      )
      &&
      (
        let (_, _, _, res) = eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Disj(e,Val(VBool True))))) in 
        (res = Val(VBool True) || res = Revert)
      )
    )
  end
)
(* De morgan e algebra bool*)


let test_if = Test.make ~name:"test if operator"
(set_shrink tshrink arb_tree_bool)
(fun (e) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let e' = match eval_expr ct vars (blockchain, blockchain, sigma, e) with 
      | (_, _, _, e) -> if e = Revert then Val(VBool False) else e 
    in 
    eval_expr ct vars (blockchain, blockchain, sigma, (If(e', e, Revert)))
    =
    eval_expr ct vars (blockchain, blockchain, sigma, (If(e', e, Revert)))
  end
)


let test_let = Test.make ~name:"test let operator"
(pair (set_shrink tshrink arb_tree_arit) (set_shrink tshrink arb_tree_arit))
(fun (e1, e2) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let (_, _, _, res) = eval_expr ct vars (blockchain, blockchain, sigma, (Let(UInt, "x", e1, e2))) in 
    let (_, _, _, valread) =  eval_expr ct vars (blockchain, blockchain, sigma, Var "x") in
    let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain, sigma, e2) in
    let (_, _, _, e1') = eval_expr  ct vars (blockchain, blockchain, sigma, e1) in 
    (valread = e1')
      &&
    (res = e2') 
  end
)  

let test_assign = Test.make ~name:"test assign operator"
(triple arb_tree_arit arb_tree_arit arb_tree_arit)
(fun (e1, e2, e3) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let (_, _, _, res) = eval_expr ct vars (blockchain, blockchain, sigma, (Let(UInt, "x", e1, Seq(Assign("x", e3),e2)))) in 
    let (_, _, _, valread) =  eval_expr ct vars (blockchain, blockchain, sigma, Var "x") in
    let (_, _, _, e3') = eval_expr ct vars (blockchain, blockchain, sigma, e3) in
    let (_, _, _, e2') = eval_expr  ct vars (blockchain, blockchain, sigma, e2) in 
    (valread = e3')
      &&
    (res = e2') 
  end
)  



let test_add_contract_to_ct = Test.make ~name:"test add contract to contract table"
(make Gen.unit)
(fun () -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = test_contract in 
    let (_, _, _, res) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    (
      (res = Val(VUnit)) && (Hashtbl.mem ct contract.name)
    )
  end
) 


let test_new_contract = Test.make ~name:"test new contract"
(arb_tree_arit)
(fun (n) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = test_contract in 
    let n' = match eval_expr ct vars (blockchain, blockchain, sigma, n) with 
      | (_, _, _, Val(VUInt n)) -> VUInt n
      |_ -> VUInt 0  
    in
    let (_, _, _, _) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    let res = match eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(n'), [Val(VAddress "0x0"); Val(n')])) with
      | (_, _, _, Val(res)) -> res
      | _ -> assert false
    in
    let address = match eval_expr ct vars (blockchain, blockchain, sigma, Address(Val(res))) with
      | (_, _, _, Val(address)) -> address
      | _ -> assert false
    in
    let (cname, sv, bal) = Hashtbl.find blockchain (res, address) in
    
    let test_var1_val = StateVars.find "test_sv1" sv in 
    let test_var2_val = StateVars.find "test_sv2" sv in 
    (
      cname = contract.name && bal = n' && 
      (
        (test_var1_val = Val(VAddress "0x0")) &&
        (test_var2_val = Val(n'))
      )
    )
  end
) 


let test_balance = Test.make ~name:"test balance function"
(arb_tree_arit)
(fun (n) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = test_contract in 
    let n' = match eval_expr ct vars (blockchain, blockchain, sigma, n) with 
      | (_, _, _, Val(VUInt n)) -> VUInt n 
      |_ -> VUInt 0  
    in
    let (_, _, _, _) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    let res = match eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(n'), [Val(VAddress "0x0"); Val(n')])) with
      | (_, _, _, Val(res)) -> res
      | _ -> assert false
    in 
    let address = match eval_expr ct vars (blockchain, blockchain, sigma, Address(Val(res))) with
      | (_, _, _, Val(address)) -> address
      | _ -> assert false
    in
    let bal = match eval_expr ct vars (blockchain, blockchain, sigma, Balance(Val(address))) with
      | (_, _, _, Val(bal)) -> bal
      | _ -> assert false
    in
    (
      bal = n'
    )
  end
) 

let test_address = Test.make ~name:"test address function"
(set_shrink tshrink arb_tree_arit)
(fun (n) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = test_contract in 
    let n' = match eval_expr ct vars (blockchain, blockchain, sigma, n) with 
      | (_, _, _, Val(VUInt n)) -> VUInt n 
      |_ -> VUInt 0  
    in
    let (_, _, _, _) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    let res = match eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(n'), [Val(VAddress "0x0"); Val(n')])) with
      | (_, _, _, Val(res)) -> res
      | _ -> assert false
    in 
    let address = match eval_expr ct vars (blockchain, blockchain, sigma, Address(Val(res))) with
      | (_, _, _, Val(address)) -> address
      | _ -> assert false
    in
    let (cname, _sv, _) = Hashtbl.find blockchain (res, address) in
    (
      cname = contract.name 
    )
  end
) 

let test_stateread = Test.make ~name:"test state read"
(set_shrink tshrink arb_tree_arit)
(fun (n) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = test_contract in 
    let n' = match eval_expr ct vars (blockchain, blockchain, sigma, n) with 
      | (_, _, _, Val(VUInt n)) -> VUInt n 
      |_ -> VUInt 0  
    in
    let (_, _, _, _) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    let (_, _, _, res) = eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(n'), [Val(VAddress "0x0"); Val(n')])) in
    (
      let (_, _, _, sr1) = eval_expr ct vars (blockchain, blockchain, sigma, StateRead(res, "test_sv1")) in 
      let (_, _, _, sr2) = eval_expr ct vars (blockchain, blockchain, sigma, StateRead(res, "test_sv2")) in 
      (sr1 = Val(VAddress "0x0")) && (sr2 = Val(n')) 
    )
  end
) 

let test_statewrite= Test.make ~name:"test state write"
(set_shrink tshrink arb_tree_arit)
(fun (n) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = test_contract in 
    let n' = match eval_expr ct vars (blockchain, blockchain, sigma, n) with 
      | (_, _, _, Val(VUInt n)) -> VUInt n 
      |_ -> VUInt 0  
    in
    let (_, _, _, _) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    let res = match eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(n'), [Val(VAddress "0x0"); Val(n')])) with
      | (_, _, _, Val(res)) -> res
      | _ -> assert false
    in 
    let address = match eval_expr ct vars (blockchain, blockchain, sigma, Address(Val(res))) with
      | (_, _, _, Val(address)) -> address
      | _ -> assert false
    in
    (
      let (blockchain, _, _, sa1) = eval_expr ct vars (blockchain, blockchain, sigma, StateAssign(Val(res), "test_sv1", Val(VAddress "0x1"))) in 
      let (blockchain, _, _, sa2) = eval_expr ct vars (blockchain, blockchain, sigma, StateAssign(Val(res), "test_sv2", Val(n'))) in 
      let (_, sv, _) = Hashtbl.find blockchain (res, address) in  

      (sa1 = Val(VAddress "0x1")) && (sa2 = Val(n')) 
      &&
      ((StateVars.find "test_sv2" sv) = Val(n'))
      &&
      ((StateVars.find "test_sv1" sv) = Val(VAddress "0x1"))
    )
  end
) 

(* let test_transfer= Test.make ~name:"test transfer function"
(set_shrink tshrink arb_tree_arit)
(fun (n) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = eoa_contract in 
    let n' = match eval_expr ct vars (blockchain, blockchain, sigma, n) with 
      | (_, _, _, Val(VUInt n)) -> VUInt n 
      |_ -> VUInt 0  
    in
    let (_, _, _, _) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    let c1 = match eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(n'), [])) with
      | (_, _, _, Val(res)) -> res
      | _ -> assert false
    in 
    let c2 = match eval_expr ct vars (blockchain, blockchain, sigma, New(contract.name, Val(VUInt 1000000), [])) with
      | (_, _, _, Val(res)) -> res
      | _ -> assert false
    in 
    let address = match eval_expr ct vars (blockchain, blockchain, sigma, Address(Val(res))) with
      | (_, _, _, Val(address)) -> address
      | _ -> assert false
    in
    (
      let (blockchain, _, _, sa1) = eval_expr ct vars (blockchain, blockchain, sigma, StateAssign(Val(res), "test_sv1", Val(VAddress "0x1"))) in 
      let (blockchain, _, _, sa2) = eval_expr ct vars (blockchain, blockchain, sigma, StateAssign(Val(res), "test_sv2", Val(n'))) in 
      let (_, sv, _) = Hashtbl.find blockchain (res, address) in  

      (sa1 = Val(VAddress "0x1")) && (sa2 = Val(n')) 
      &&
      ((StateVars.find "test_sv2" sv) = Val(n'))
      &&
      ((StateVars.find "test_sv1" sv) = Val(VAddress "0x1"))
    )
  end
)  *)




let test_suite = [
  test_division_by_zero; 
  test_arit_op; 
  test_bool_op;
  test_if;
  test_let;
  test_assign;
  test_add_contract_to_ct;
  test_new_contract;
  test_arit_plus_op;
  test_arit_minus_op;
  test_arit_times_op;
  test_arit_div_op;
  test_balance;
  test_address;
  test_stateread;
  test_statewrite
] 

let () =

  (* Generate string  with gen*)
  (* gen_string |> Gen.generate1 |> print_endline; *)


  let suite =
    List.map QCheck_alcotest.to_alcotest
      test_suite
  in
  Alcotest.run "FS Operational Semantics Tests" [
    "suite", suite
  ]
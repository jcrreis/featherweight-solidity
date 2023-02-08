open QCheck
open Featherweightsolidity 
open Fs 


let leafgen_int = Gen.oneof[ Gen.map (fun i -> Val(VUInt i)) Gen.int]

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

let leafgen_bool = Gen.oneof[ Gen.map (fun b -> if b then Val(VBool True) else Val(VBool False)) Gen.bool]

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



(* 
let conf: conf = (blockchain, blockchain, sigma, e) in *)

let arb_tree_arit = make ~print:expr_to_string (gen_arit_op_ast 8)

let arb_tree_bool = make ~print:expr_to_string (gen_bool_op_ast 8)

let test_division_by_zero = Test.make ~name:"test eval_expr"
  (arb_tree_arit)
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

let test_arit_op = Test.make ~name:"test eval_expr"
  (arb_tree_arit)
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


let test_bool_op = Test.make ~name:"test eval_expr"
(arb_tree_bool)
(fun (e) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Conj(e,e))))
    =
    eval_expr ct vars (blockchain, blockchain, sigma, (BoolOp(Disj(e,e))))
  end
)

let test_if = Test.make ~name:"test eval_expr"
(arb_tree_bool)
(fun (e) -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    eval_expr ct vars (blockchain, blockchain, sigma, (If(Val(VBool True), e, Revert)))
    =
    eval_expr ct vars (blockchain, blockchain, sigma, (If(Val(VBool False), Revert, e)))
  end
)


let test_let = Test.make ~name:"test eval_expr"
(pair arb_tree_arit arb_tree_arit)
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

let test_assign = Test.make ~name:"test eval_expr"
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

(* 
| AddContract cdef -> 
  begin 
    let fun_names = (List.map (fun (f_def) -> f_def.name) cdef.functions) in
    if List.mem "fb" fun_names || List.mem "receive" fun_names
    then 
    begin
      Hashtbl.add ct cdef.name cdef; (blockchain, blockchain', sigma, Val(VUnit))
    end
    else 
      (blockchain, blockchain', sigma, Revert)
  end *)

(* let test_add_contract_to_ct = Test.make ~name:"test eval_expr"
(* () *)
(fun () -> 
  begin 
    let ct = Hashtbl.create 64 in 
    let vars = Hashtbl.create 64 in 
    let blockchain = Hashtbl.create 64 in  
    let sigma = Stack.create() in 
    let contract: contract_def = bank_contract() in 
    let (_, _, _, res) =  eval_expr ct vars (blockchain, blockchain, sigma, AddContract(contract)) in 
    (
      (res = Val(VUnit)) && (Hashtbl.mem ct contract.name)
    )
  end *)
(* )  *)

let test_suite = [
  test_division_by_zero; 
  test_arit_op; 
  test_bool_op;
  test_if;
  test_let;
  test_assign
  (* test_add_contract_to_ct *)
] 

let () =
  let errcode = QCheck_runner.run_tests_main test_suite in 
  exit errcode

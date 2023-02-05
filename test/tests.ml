open Featherweightsolidity  
open Fs 

let test_arit_ops = assert false 

let test_bool_ops = assert false 


let test_if = 
  let _e1 = If(Val(VBool True), Val(VBool True), Val(VBool False)) in 
  let _e2 = If(Val(VBool False), Val(VBool True), Val(VBool False)) in 

  assert false

let test_var = assert false 

let test_new = assert false

let test =
  QCheck.Test.make ~count:1000 ~name:"list_rev_is_involutive"
   QCheck.(list small_nat)
   (fun l -> List.rev (List.rev l) = l);;

(* we can check right now the property... *)
QCheck.Test.check_exn test;;

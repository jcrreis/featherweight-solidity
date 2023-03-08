(*
 * ocamlbuild c3.native
 *)
(*https://github.com/Leonidas-from-XIV/sandbox/blob/master/c3.ml*)

(*
The head_not_in_tails function returns the first element of each list and checks if it is not present in the tail of any of the lists. This is an important check to avoid the diamond inheritance problem.

The merge function recursively removes a class from the list of lists of parents until there is no class that can be removed without violating the ordering constraints.

The c3_exn function recursively computes the C3 linearization of a class by merging the C3 linearizations of its parents and adding the class itself.

Finally, the c3 function returns the C3 linearization of a class if it exists, and None otherwise.   
*)
open Types

let head = function
| [] -> []
| x -> [List.hd x]

let tail = function
| [] -> []
| x -> [List.tl x]

let concat_map f l = List.concat @@ List.map f l

let head_not_in_tails (l : string list list) =
let heads = concat_map head l in
let tails = concat_map tail l in
let find_a_head_that_is_not_in_tails acc v = match acc with
  | Some x -> Some x
  | None -> if List.exists (List.mem v) tails then None else Some v
in
List.fold_left find_a_head_that_is_not_in_tails None heads


let remove to_remove l =
let rem to_remove = List.filter (fun e -> e != to_remove) in
rem [] @@ List.map (rem to_remove) l

exception No_linearization

let rec merge (l : string list list) =
match head_not_in_tails l with
| Some c -> (match remove c l with
  | [] -> [c]
  | n -> c :: merge n)
| None -> raise No_linearization


let rec c3_linearization (contract: string) (ct: contract_table) : string list =
  let contract_def: contract_def = Hashtbl.find ct contract in 
  match contract_def.super_contracts with 
    | [] -> [contract]
    | parents -> 
      let parent_lists = List.map (fun parent -> c3_linearization parent ct) parents in
      let all_parents = parents :: parent_lists in
      [contract] @ merge all_parents

(*https://github.com/Leonidas-from-XIV/sandbox/blob/master/c3.ml*)
(*https://medium.com/coinmonks/inheritance-in-solidity-debunked-3d8dd32d3a99*)
(*https://docs.soliditylang.org/en/v0.8.15/contracts.html#multiple-inheritance-and-linearization*)
(*
The head_not_in_tails function returns the first element of each list and checks if 
  it is not present in the tail of any of the lists. 
This is an important check to avoid the diamond inheritance problem.

The merge function recursively removes a class from the list of lists of parents until there is 
no class that can be removed without violating the ordering constraints.

The c3_exn function recursively computes the C3 linearization of a class by 
merging the C3 linearizations of its parents and adding the class itself.

Finally, the c3 function returns the C3 linearization of a class if it exists, and None otherwise.   
*)

(*
python semantics

https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=055708e7d53226e1da480f76796ac58f15f8abdc
https://www.python.org/download/releases/2.3/mro/
*)
open Types
module SS = Set.Make(String)

let head = function
| [] -> []
| x -> [List.hd x]

let tail = function
| [] -> []
| x -> [List.tl x]

(*This function first applies f to each element in l using List.map,
    resulting in a list of lists. 
    The @@ operator then concatenates all these lists together into a single list using List.concat.*)

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

let c3_linearization (contract: string) (ct: contract_table) : string list =
  let visited = SS.empty in        
  let rec compute_linearization (contract: string) (ct: contract_table) (visited: SS.t) : string list =
    let contract_def: contract_def = Hashtbl.find ct contract in 
    match contract_def.super_contracts with 
      | [] -> [contract]
      | parents -> 
        let parent_lists = (List.map (fun parent -> 
          if SS.mem parent visited then 
            raise (Failure "Mutually recursive inheritance detected")
          else
            compute_linearization parent ct (SS.union visited (SS.singleton parent))) parents) in
        let all_parents = parents :: parent_lists in
        [contract] @ merge all_parents
  in 
  compute_linearization contract ct visited 



(* In Solidity, multiple inheritance is implemented using a linearization algorithm called the "C3 Linearization". 
This algorithm is used to determine the order in which the base contracts should be searched 
when resolving function calls and variable references.

When a contract inherits from two or more base contracts that have state variables or functions with the same name, 
Solidity uses the same approach as other object-oriented languages:
 the derived contract must provide an explicit override for the conflicting item or resolve the conflict in some other way.

To resolve function name conflicts, the derived contract can use explicit function call notation to specify which function to call.
 For example, if both A and B define a function foo, and C inherits from both A and B, it can call A.foo() or B.foo() 
  explicitly to disambiguate between the two functions.

Similarly, to resolve variable name conflicts, the derived contract can use explicit variable access notation to 
specify which variable to access. For example, if both A and B define a variable x, and C inherits from both A and B, it 
  can access A.x *)


(* 
Let's define C3 as a function that takes a list of parent classes and returns a linearized list of these classes:

C3(parents) = linearized_list

To find the linearization of a list of classes, we first need to define a merge function, which takes two linearized lists and merges them into a single list:

merge(list1, list2) = merged_list

Now we can define the C3 function using the following recursive algorithm:

If parents is empty, return an empty list.

Otherwise, let H be the first element of parents, and let T be the rest of the list.

Recursively call C3 on T, and let L be the result.

Merge the linearized list of H and L using the merge function:

merged_list = merge(linearized_list(H), L)

Return the merged list.

The merge function can be defined as follows:

If list1 is empty, return list2.

If list2 is empty, return list1.

Let h1 be the head of list1, and t1 be the tail.

Let h2 be the head of list2, and t2 be the tail.

If h1 is not in list2 and h2 is not in list1, add h1 to the beginning of the merged list, and merge t1 and list2.

Otherwise, if h1 is not in list2, add h1 to the beginning of the merged list, and merge t1 and list2.

Otherwise, if h2 is not in list1, add h2 to the beginning of the merged list, and merge list1 and t2.

Otherwise, raise a NoLinearization exception.

This definition follows the same recursive algorithm used in the code implementation we've been discussing, but it is presented mathematically instead. *)
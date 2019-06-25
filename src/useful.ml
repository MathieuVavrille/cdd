open Bdd
   
(**********************************)
(* Some useful string conversions *)

let string_of_array f a =
  "["^(Array.fold_left (fun acc x -> acc^(f x)^";") "" a)^"]" 
              
let string_of_list f l = "["^(List.fold_left (fun acc elt -> acc^(f elt)^";") "" l)^"]"

                       
(**********************)
(* Module definitions *)

(* Set of BDD using the structural equality/comparison *)
module Orderedbdd =
  struct
    type t = bdd
    let compare = bdd_compare
  end

module Bddset = Set.Make(Orderedbdd)

let string_of_bddset b = 
  "{"^(Bddset.fold (fun elt acc -> string_of_bdd elt^" ; "^acc) b "")^"}"

module Bddsmap = Map.Make(Bddset)

               
module OrderedBitVector =
  (* Actually a bit-list *)
  struct
    type t = bool list
    let rec compare l1 l2 = match l1, l2 with
      | [], [] -> 0
      | false::_, true::_ -> -1
      | true::_, false::_ -> 1
      | _::q1, _::q2 -> compare q1 q2
      | [], _ -> -1
      | _, [] -> 1
  end

(* Set of bit-vectors *)
module Bvset = Set.Make(OrderedBitVector)

let string_of_bvset b =
  "{"^(Bvset.fold (fun elt acc -> string_of_list string_of_bool elt^" ; "^acc) b "")^"}"

module Bvsetset = Set.Make(Bvset)

let string_of_bvsetset b = 
  "{"^(Bvsetset.fold (fun elt acc -> string_of_bvset elt^" ; "^acc) b "")^"}"

                
module Orderedbddbddlist =
  struct
    type t = bdd * Bddset.t
    let compare (m1,m2) (m1', m2') =
      match Pervasives.compare (ref m1) (ref m1') with
      | 0 -> Bddset.compare m2 m2'
      | a -> a
  end
  
module Bddbddsset = Set.Make(Orderedbddbddlist)

module Strmap = Map.Make(String)

module Strset = Set.Make(String)
              
module Intset = Set.Make(struct type t = int let compare = Pervasives.compare end)

module Intmap = Map.Make(struct type t = int let compare = Pervasives.compare end)
              
(* Functions to create or extract bdds *)
               
let bitvect_of_int integer size =
  (* Get the binary representation of an integer on size bits *)
  let rec aux acc integer size =
    match size with
    | 0 -> acc
    | _ -> aux ((integer mod 2 = 1)::acc) (integer/2) (size - 1)
  in aux [] integer size

let split_zero_one_bvset set =
  (* Splits a bit-list set into the ones that starts with zero and the ones that start with one *)
  Bvset.fold
    (fun elt (zero, one) -> match elt with
                            | [] -> (zero, one)
                            | true::q -> (zero, Bvset.add q one)
                            | false::q -> (Bvset.add q zero, one)
    ) set (Bvset.empty, Bvset.empty)
  
let rec bdd_of_bitvectset set =
  (* Returns the bdd representing the bitlistset *)
  match Bvset.is_empty set with
  | true -> F
  | false ->
     match Bvset.exists (fun x -> x != []) set with
     | true -> let (zero, one) = split_zero_one_bvset set in
               bdd_of (bdd_of_bitvectset zero) (bdd_of_bitvectset one)
     | false -> T

let bdd_of_intlist l size =
  (* Return the bdd representing the list of integers represented on -size- bits *)
  bdd_of_bitvectset (List.fold_left (fun acc elt ->
                     Bvset.add (bitvect_of_int elt size) acc) Bvset.empty l)

let bdd_of_int integer size depth =
  (* Return the bdd representing a single integer (on size bits) and the bdd have depth depth *)
  let rec aux acc integer size depth =
    match size, depth with
    | 0, 0 -> acc
    | 0, _ -> aux (bdd_of acc acc) 0 0 (depth - 1)
    | _, _ -> aux (if integer mod 2 = 0 then bdd_of acc F else bdd_of F acc) (integer/2) (size-1) (depth-1)
  in
  aux T integer size depth
   
let bitvectset_of_bdd =
  (* Returns the bitlistset represented by the bdd *)
  let computed = Hashtbl.create 101 in
  let rec aux t =
    try Hashtbl.find computed (ref t)
    with Not_found ->
          let res = match t with
            | F -> Bvset.empty
            | T -> Bvset.add [] Bvset.empty
            | N(a,b) -> Bvset.union (Bvset.map (fun l -> false::l) (aux a)) (Bvset.map (fun l -> true::l) (aux b))
          in
          Hashtbl.add computed (ref t) res;
          res
  in aux

(* Conversion functions *)
let int_of_bitvect = List.fold_left (fun acc elt -> 2*acc+(if elt then 1 else 0)) 0

let intlist_of_bitvectset bvset = Bvset.fold (fun elt acc -> int_of_bitvect elt::acc) bvset []

let int_of_bdd m =
  (* Returns the integer corresponding to the BDD, raises an error if it is not possible (not a singleton BDD) *)
  let rec aux m acc = match m with
    | T -> acc
    | F -> failwith "int_of_bdd: Can't give int from empty set"
    | N(a,F) -> aux a (2*acc)
    | N(F,a) -> aux a (2*acc+1)
    | _ -> failwith "int_of_bdd: Can't give int from set with multiple values"
  in aux m 0

let rec pow a n =
  (* naive power *)
  match n with
  | 0 -> 1
  | n -> a*(pow a (n-1))
       
let random_set max =
  (* This function generates bdds of mean cardinal 2^{max-1}, which may not be representative *)
  let rec aux acc current =
    match current with
    | -1 -> acc
    | _ -> match Random.bool () with
           | true -> aux (Bvset.add (bitvect_of_int current max) acc) (current-1)
           | false -> aux acc (current-1)
  in
  aux Bvset.empty (pow 2 max)



(***********************************************************)
(* Functions to cut BDDs, extend them, or concatenate them *)
            
let possible_outputs m bdd_fun =
  (* Return the set of BDDs that are the got by following a path in the bdd_fun that is also in m *)
  let rec aux m current_bdd_fun acc = match m,current_bdd_fun with
    | F,_ | _, F -> acc
    | T, _ -> Bddset.add current_bdd_fun acc
    | N(a,b), N(c,d) -> aux a c (aux b d acc)
    | N _, _ -> failwith "possible_outputs: the bdd_fun is not big enough"
  in
  aux m bdd_fun Bddset.empty
  
let complete_bdd =
  let hash_complete = Hashtbl.create 23 in
  let rec aux depth =
    try Hashtbl.find hash_complete depth
    with Not_found -> 
      let res = (* Returns the complete BDD of given depth *)
        match depth with
        | 0 -> T
        | _ -> let current = aux (depth-1) in bdd_of current current in
      Hashtbl.add hash_complete depth res;
      res
  in aux

let cutted_bdd =
  (* Return the BDD where we keep only the first bits *)
  let computed = Hashtbl.create 101 in
  let rec aux wanted_depth m =
    if depth m <= wanted_depth then m else begin
        try Hashtbl.find computed (ref m,wanted_depth)
        with Not_found ->
          let res = match wanted_depth, m with
            | _, F -> F
            | 0, _ -> T
            | _, T -> failwith "cutted_bdd: wanted to cut a bdd that is too small"
            | _, N(a,b) -> bdd_of (aux (wanted_depth-1) a) (aux (wanted_depth-1) b) in
          Hashtbl.add computed (ref m, wanted_depth) res;
      res end in
  aux

let concatenate_bdd = 
  (* Return the bdd representing the concatenation of the two bdds *)
  let computed = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find computed (ref m, ref m')
    with Not_found ->
      let res = match m with
        | T -> m'
        | F -> F
        | N(a,b) -> bdd_of (aux a m') (aux b m') in
      Hashtbl.add computed (ref m, ref m') res;
      res in
  aux

let complete_end depth m =
  (* Add the complete BDD at the end of the chosen BDD *)
  let full_bdd = complete_bdd depth in
  concatenate_bdd m full_bdd

let give_depth wanted_depth m =
  (* either reduce or increase the depth of the given BDD. Decreasing will remove the lower part, increasing will add the complete BDD at the end *)
  let current_depth = depth m in
  let res = 
  if wanted_depth > current_depth then
    complete_end (wanted_depth - current_depth) m
  else
    cutted_bdd wanted_depth m
  in
  if depth res <> wanted_depth then failwith "give_depth: not good depth (the input BDD probably have depth 0 (=F)" else res



(*****************************************************)
(* Saving, printing in dot and uploading from a file *)
  
let dot_file m filename =
  (* Outputs a string that can be processed with graphviz dot *)
  (* Warning, for big graphs the computation of graphviz can be long *)
  let s = ref "graph g {\n" in
  let counter = let x = ref (-1) in fun () -> incr x; !x in
  let indices = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find indices (ref m)
    with Not_found -> 
          let c = counter() in
          Hashtbl.add indices (ref m) c;
          match m with
          | T -> s := !s^""^(string_of_int c)^" [label=\"\",shape=plaintext,width=.1,height=0];\n";c
          | F -> c
          | N(F,b) -> s := !s^(string_of_int c)^" [label=\"\",shape=plaintext,width=.5,height=0];\n";
                      let cb = aux b in
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int cb)^";\n";
                      c
          | N(a,F) -> s := !s^(string_of_int c)^" [label=\"\",shape=plaintext,width=.5,height=0];\n";
                      let ca = aux a in
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int ca)^" [style=dotted];\n";
                      c
          | N(a,b) -> s := !s^(string_of_int c)^" [label=\"\",shape=plaintext,width=.5,height=0];\n";
                      let cb, ca = aux b, aux a in
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int cb)^";\n";
                      s := !s^""^(string_of_int c)^" -- "^(string_of_int ca)^" [style=dotted];\n";
                      c
  in
  let _ = aux m in
  s := !s^"}";
  let open Printf in
  let oc = open_out filename in
  fprintf oc "%s\n" !s;
  close_out oc

let save_to_file m filename =
  (* Saves the bdd to the file given by filename. The format is special, it should be used with get_from_file *)
  (* The BDD 0 is T, 1 is F, and 2 is the main BDD *)
  let counter = let x = ref 1 in fun () -> incr x; !x in
  let index = Hashtbl.create 101 in
  Hashtbl.add index (ref T) 0;
  Hashtbl.add index (ref F) 1;
  let s = ref "" in
  let rec aux m =
    try Hashtbl.find index (ref m)
    with Not_found ->
          match m with
          | T -> 0
          | F -> 1
          | N(a,b) ->
             let current_count = counter () in
             Hashtbl.add index (ref m) current_count;
             let ai, bi = aux a, aux b in
             s := !s^(string_of_int current_count)^":"^(string_of_int ai)^","^(string_of_int bi)^";";
             current_count
  in
  let _ = aux m in
  let open Printf in
  let oc = open_out filename in
  fprintf oc "%s" !s;
  close_out oc
  
let get_from_file filename =
  (* Takes as input the name of the file to open, open it and return the corresponding bdd *)
  let ic = open_in filename in
  let text = input_line ic in
  close_in ic;
  let full_map = List.fold_left (fun acc elt -> if elt = "" then acc else begin
                                     match String.split_on_char ':' elt with
                                     | x::[y] -> let a,b = match String.split_on_char ',' y with
                                                   | astr::[bstr] -> Strmap.find astr acc, Strmap.find bstr acc
                                                   | _ -> failwith "second error on the file"
                                                 in
                                                 Strmap.add x (bdd_of a b) acc
                                     | _ -> failwith "error on the file"
                                                  end ) (Strmap.add "0" T (Strmap.singleton "1" F)) (String.split_on_char ';' text) in
  Strmap.find "2" full_map


  
(* Some other useful functions *)

let rec list_compare f l1 l2 = match l1, l2 with
  | [], [] -> 0
  | _, [] -> -1
  | [], _ -> 1
  | x::q, y::r -> match f x y with
                  | 0 -> list_compare f q r
                  | n -> n

                       
let inter_of_union =
  (* Computes the intersection of the first parameter with the union of the set (second parameter) *)
  let computed = Hashtbl.create 101 in
  let split_zero_one bdds =
    (* Take a bddset as input and return two bddsets: one with all the 0-subtrees, and the other with all the 1-subtrees *) 
    Bddset.fold (fun elt (zeroacc, oneacc) ->
        match elt with
        | T -> failwith "split_zero_one_inter_with_union: not the same size"
        | F -> (zeroacc, oneacc)
        | N(F,F) -> failwith "inter_with_union : N(F,F) should be equal to F"
        | N(F,c) -> (zeroacc, Bddset.add c oneacc)
        | N(c,F) -> (Bddset.add c zeroacc, oneacc)
        | N(c,d) -> (Bddset.add c zeroacc, Bddset.add d oneacc)
      ) bdds (Bddset.empty, Bddset.empty)
  in
  let rec aux bdd bdds =
    try Bddsmap.find bdds (Hashtbl.find computed (ref bdd))
    with Not_found ->
      let res = match bdd, Bddset.is_empty bdds with
        | F, _ | _, true -> F
        | T, false -> T 
        | N(a,b), false -> 
           let zero, one = split_zero_one bdds in
           bdd_of (aux a zero) (aux b one)
      in
      (* add the element in the table *)
      Hashtbl.add computed (ref bdd) (try Bddsmap.add bdds res (Hashtbl.find computed (ref bdd))
                                      with Not_found -> Bddsmap.singleton bdds res);
      res in
  aux

(* if the minimum value of the bdd is c, generates [c,+oo] *)
let lower_bound =
  let hash_lower = Hashtbl.create 101 in
  let rec aux b =
    try Hashtbl.find hash_lower (ref b)
    with Not_found ->
      let res = match b with
        | T -> T
        | F -> failwith "Can' generate lower bound of empty bdd"
        | N(F,a) -> bdd_of F (aux a)
        | N(a,c) -> bdd_of (aux a) (complete_bdd (depth c)) in
      Hashtbl.add hash_lower (ref b) res;
      res
  in aux 


(* if the max value of the bdd is c, generates [0,c] *)
let upper_bound =
  let hash_upper = Hashtbl.create 101 in
  let rec aux b =
    try Hashtbl.find hash_upper (ref b)
    with Not_found ->
      let res = match b with
        | T -> T
        | F -> failwith "Can' generate lower bound of empty bdd"
        | N(a,F) -> bdd_of (aux a) F
        | N(c,a) -> bdd_of (complete_bdd (depth c)) (aux a) in
      Hashtbl.add hash_upper (ref b) res;
      res
  in aux 

(************************************)
(* Useful constants or special BDDs *)

let complete8 = complete_bdd 8
              
let complete16 = complete_bdd 16
               
let zero_bdd8 = bdd_of_int 0 8 8
              
let zero_bdd16 = bdd_of_int 0 16 16
               
let not_zero_bdd8 = diff (complete_bdd 8) (bdd_of_int 0 8 8)
                      

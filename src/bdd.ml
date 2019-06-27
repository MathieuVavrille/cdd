module B = Big_int_Z
                
(* BDDs are trees and nodes have a 0-edge (first of the couple) and a 1-edge (second element of the couple) *)
type bdd = T | F | N of bdd * bdd
                      
(* The hashtable that will contain all the trees *)
let main_hash = Hashtbl.create 101

(* Ensures that N(F,F) = F *)
let _ = Hashtbl.add main_hash (ref F,ref F) F

(* One should never use the N constructor but this one instead (to ensure maximal sharing) *)
let bdd_of =
  let main_hash = Hashtbl.create 101 in
  Hashtbl.add main_hash (ref F,ref F) F;
  let aux a b = 
    try Hashtbl.find main_hash (ref a,ref b)
    with Not_found -> let t = N(a,b) in Hashtbl.add main_hash (ref a,ref b) t; t in
  aux

(* Now that we ensure structural equality, we can use it *)
let bdd_compare m1 m2 = Pervasives.compare (ref m1) (ref m2)

let is_leaf m = match m with
  | T | F -> true
  | _ -> false

let is_empty m =
  m == F
       
(* Conversion function *)
let rec string_of_bdd t = match t with
  | T -> "T"
  | F -> "F"
  | N(a,b) -> "N("^(string_of_bdd a)^","^(string_of_bdd b)^")"


  module T = Big_int_Z
            
let depth_card  =
  (* Returns the depth of the bdd and the cardinality of the set it represents (bounded by max_int, bigger than this will return max_int *)
  let data = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find data (ref m)
    with Not_found ->
      let res = match m with
        | T -> (0,B.unit_big_int)
        | F -> (0,B.zero_big_int)
        | N(a,b) -> let (d1,c1),(d2,c2) = aux a, aux b in
                    (max d1 d2+1, B.add_big_int c1 c2)
      in
      Hashtbl.add data (ref m) res;
      res
  in aux
   
(* These two functions return in constant time amortized (I think, if there is a lot of accesses) *)   
let depth m = fst (depth_card m)

let cardinal m = snd (depth_card m)

let array_width m =
  (* Give the width of each layer of a bdd in an array*)
  let visited = Hashtbl.create 101 in
  Hashtbl.add visited (ref F) ();
  (* At the index d there is the width of the depth d *)
  let widths = Array.make (depth m + 1) 0 in
  let rec aux m =
    try Hashtbl.find visited (ref m)
    with Not_found ->
          Hashtbl.add visited (ref m) ();
          widths.(depth m) <- widths.(depth m) + 1;
          match m with
          | T | F -> ()
          | N(a,b) -> let _ = aux a, aux b in ()
  in
  aux m;
  widths

let width m = Array.fold_left (fun acc elt ->
      max acc elt
    ) 0 (array_width m)

(********************************)
(* Set theoretics, uses caching, and will surely increase the width *)
  
let intersection =
  (* The intersection of two bdds *)
  let inter_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find inter_hash (ref m,ref m')
    with Not_found ->
      let t = match m, m' with
        | F, _ | _, F-> F
        | T, T -> T
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
        | _ -> failwith "intersection: the BDDs do not have the same depth"
      in
      Hashtbl.add inter_hash (ref m,ref m') t;
      t
  in aux

let union =
  (* The union of two bdds. *)
  let union_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find union_hash (ref m,ref m')
    with Not_found ->
      let t = match m, m' with
        | _, T | T, _ -> T
        | F, _ -> m'
        | _, F -> m
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add union_hash (ref m,ref m') t;
      t
  in aux

let diff =
  (* The difference of two bdds. Can increase the width *)
  let diff_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find diff_hash (ref m,ref m')
    with Not_found ->
      let t = match m, m' with
        | _, T | F, _ -> F
        | _, F -> m
        | T, N _ -> failwith "diff: the bdds does not have the same size"
        | N(a,b), N(c,d) -> bdd_of (aux a c) (aux b d)
      in
      Hashtbl.add diff_hash (ref m,ref m') t;
      t
  in aux

let subset =
  (* Returns true if the first arg is a subset of the second arg *)
  let subset_hash = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find subset_hash (ref m,ref m')
    with Not_found ->
      let res = match m, m' with
        | F, _ | _, T -> true
        | _, F -> false
        | T, N _ -> failwith "subset: the bdds does not have the same size"
        | N(a,b), N(c,d) -> (aux a c) && (aux b d)
      in
      Hashtbl.add subset_hash (ref m,ref m') res;
      res
  in aux

let equal m m' = bdd_compare m m' = 0
   
(**********************)
(* Bitwise operations *)   

let bdd_not =
  let hash_not = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find hash_not (ref m)
    with Not_found ->
          let res =
            match m with
            | N(a,b) -> bdd_of (aux b) (aux a)
            | _ -> m
          in
          Hashtbl.add hash_not (ref m) res;
          res
  in aux
  
let bdd_and =
  let hash_and = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_and (ref m,ref m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> T
            | F,_ | _,F -> F
            | T,_ | _,T -> failwith "bdd_and: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (union (aux a c) (union (aux a d) (aux b c))) (aux b d)
          in
          Hashtbl.add hash_and (ref m,ref m') res;
          res
  in aux
  
let bdd_or =
  let hash_or = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_or (ref m,ref m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> T
            | F,_ | _,F -> F
            | T,_ | _,T -> failwith "bdd_and: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (aux a c) (union (aux a d) (union (aux b c) (aux b d)))
          in
          Hashtbl.add hash_or (ref m,ref m') res;
           res
  in aux
  
let bdd_xor =
  let hash_xor = Hashtbl.create 101 in
  let rec aux m m' =
    try Hashtbl.find hash_xor (ref m,ref m')
    with Not_found ->
          let res =
            match m, m' with
            | T, T -> T
            | F,_ | _,F -> F
            | T,_ | _,T -> failwith "bdd_xor: not the same depth"
            | N(a,b), N(c,d) -> bdd_of (union (aux a c) (aux b d)) (union (aux a d) (aux b c))
          in
          Hashtbl.add hash_xor (ref m,ref m') res;
          res
  in aux




       

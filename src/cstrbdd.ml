open Bdd
open Useful

let multiple_mdd_consistency m bdds =
  (* ensures MDD consistency on m wrt m' and returns m *)
  let zero_support = Hashtbl.create 101 in (* all the nodes whose 0-edge is consistent *)
  let one_support = Hashtbl.create 101 in (* all the nodes whose 1-edge is consistent *)
  let inter = Hashtbl.create 101 in (* just a set, but faster by using hashtbl *)
  let rec search_support m m' =
    try Hashtbl.find inter (ref m,ref m')
    with Not_found -> 
          match m, m' with
          | F, _ | _, F -> F
          | T, _ -> m'
          | N(_,_), T -> failwith "mdd_consistency: the bdds do not have the same size"
          | N(a,b), N(c,d) ->
             let e,f = search_support a c, search_support b d in
             let new_bdd = bdd_of e f in
             Hashtbl.add inter (ref m,ref m') new_bdd;
             begin
               match e, f with
               | F, F -> new_bdd
               | F, _ -> Hashtbl.add one_support (ref m) (); new_bdd
               | _, F -> Hashtbl.add zero_support (ref m) (); new_bdd
               | _ -> Hashtbl.add zero_support (ref m) (); Hashtbl.add one_support (ref m) (); new_bdd
             end
  in
  Bddset.iter (fun m' -> let _ = search_support m m' in ()) bdds;
  let computed = Hashtbl.create 101 in
  let rec aux2 m =
    try Hashtbl.find computed (ref m)
    with Not_found -> 
          match m with
          | F -> F
          | T -> T
          | N(a,b) ->
             let res = 
               match Hashtbl.find_opt zero_support (ref m), Hashtbl.find_opt one_support (ref m) with
               | None, None -> F
               | None, Some _ -> bdd_of F (aux2 b)
               | Some _, None -> bdd_of (aux2 a) F
               | Some _, Some _ -> bdd_of (aux2 a) (aux2 b)
             in
             Hashtbl.add computed (ref m) res;
             res
  in aux2 m

let mdd_consistency m m' = multiple_mdd_consistency m (Bddset.singleton m')




 
(* Split functions: returns two disjoint BDDs such that the union of them is the original BDD *)
      
let rec split_backtrack_first m =
  (* Split the bdd into two disjoint bdds such that the union of them is the original bdd *)
  match m with
  | T | F -> failwith "split_backtrack: The BDD has cardinal 1 (or maybe 0) and can't be splitted"
  | N(T,T) -> bdd_of T F, bdd_of F T
  | N(b,a) when is_leaf b -> let c,d = split_backtrack_first a in
                             bdd_of b c, bdd_of b d
  | N(a,b) when is_leaf b -> let c,d = split_backtrack_first a in
                             bdd_of c b, bdd_of d b
  | N(a,b) -> bdd_of a F, bdd_of F b

let split_backtrack_at_depth m d =
  let computed = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find computed (ref m)
    with Not_found ->
          let res = match depth m = d, m with
            | _, T -> failwith "split_backtrack_at_depth: depth too high"
            | _, F -> F,F
            | false, N(a,b) -> let (aa,ab), (ba,bb) = aux a, aux b in
                               bdd_of aa ba,bdd_of ab bb
            | true, N(a,b) -> bdd_of a F,bdd_of F b
          in
          Hashtbl.add computed (ref m) res;
          res
  in
  aux m

let split_backtrack_optimal_width m =
  let rec aux (best_val, best_couple) current_depth =
    match current_depth with
    | 0 -> (best_val, best_couple)
    | _ -> let a,b = split_backtrack_at_depth m current_depth in
           let split_val = Array.fold_left (fun acc elt -> acc + elt) (Array.fold_left (fun acc elt -> acc + elt) 0 (array_width a)) (array_width b) in
           aux (if split_val < best_val then (split_val, (a,b)) else (best_val, best_couple)) (current_depth-1)
  in
  snd (aux (max_int, (F,F)) (depth m))

let split_backtrack_optimal_next_width m =
  let zero_one_at_depth = Array.make (depth m + 1) (Bddset.empty, Bddset.empty) in
  let visited = Hashtbl.create 101 in
  let rec fill m =
    try Hashtbl.find visited (ref m)
    with Not_found ->
          Hashtbl.add visited (ref m) ();
          match m with
          | T | F -> ()
          | N(a,b) ->
             let z, o = zero_one_at_depth.(depth m) in
             zero_one_at_depth.(depth m) <- (if is_leaf a then z else Bddset.add a z), if is_leaf b then o else Bddset.add b o;
             fill a;
             fill b;
  in
  fill m;
  let a_width = array_width m in
  let max_val = ref (-1) in
  let max_depth = ref (-1) in
  for i = 1 to depth m do
    let (b1,b2) = zero_one_at_depth.(i) in
    let nb_merged = 2*a_width.(i) - (Bddset.cardinal b1) - (Bddset.cardinal b2) in
    (*print_endline ("nb_m "^(string_of_int nb_merged)^" i = "^(string_of_int i)^" ");*)
    if !max_val <= nb_merged && (not (Bddset.is_empty b1)) && (not (Bddset.is_empty b2))
    then (max_val := nb_merged; max_depth := i)
  done;
  if !max_val = -1 then failwith "Can't split the bdd" else split_backtrack_at_depth m (!max_depth)


  
  
let increase_value hash key value =
    Hashtbl.add hash key (B.add_big_int value (try Hashtbl.find hash key with Not_found -> B.zero_big_int))
  
let rec replace_chain hash start reference =
  (* I have a hashtable that changes bdds into others, and I have to do it many times *)
  try let x = Hashtbl.find hash (reference start) in
      match Pervasives.compare x start with
      | 0 -> start
      | _ -> replace_chain hash x reference
  with Not_found -> start
        
let limit m width heuristic = (* suppose that width >= 1 *)
  (* This function takes as input a bdd, and returns a limited-width bdd overapproximating the previous one *)
  let nb_paths_to = Hashtbl.create 101 in
  Hashtbl.add nb_paths_to (ref m) B.unit_big_int;
  let replace = Hashtbl.create 101 in
  let rec reduce layer = match Bddset.cardinal layer with
    | n when n <= width -> layer
    | _ -> let (m1, m2) = heuristic layer nb_paths_to in
           let uni = union m1 m2 in
           if uni != m1 then begin increase_value nb_paths_to (ref uni) (Hashtbl.find nb_paths_to (ref m1));
                                   Hashtbl.add replace (ref m1) uni end;
           if uni != m2 then begin increase_value nb_paths_to (ref uni) (Hashtbl.find nb_paths_to (ref m1));
                                   Hashtbl.add replace (ref m2) uni end;
           reduce (Bddset.add uni (Bddset.remove m1 (Bddset.remove m2 layer)))
  in
  let rec aux layer = match Bddset.cardinal layer with
    | 0 -> ()
    | _ -> aux (Bddset.fold (
                    fun elt acc -> match elt with
                                   | T | F | N(T,T) | N(T,F) | N(F,T) | N(F,F) -> acc
                                   | N(T, a) | N(F,a) | N(a,T) | N(a,F) -> increase_value nb_paths_to (ref a) (Hashtbl.find nb_paths_to (ref elt));
                                                                           Bddset.add a acc
                                   | N(a,b) -> increase_value nb_paths_to (ref a) (Hashtbl.find nb_paths_to (ref elt));
                                               increase_value nb_paths_to (ref b) (Hashtbl.find nb_paths_to (ref elt));
                                               Bddset.add a (Bddset.add b acc)
                  )(reduce layer) Bddset.empty)
  in
  aux (Bddset.singleton m);
  let visited = Hashtbl.create 101 in
  let rec replace_bdd m =
    try Hashtbl.find visited (ref m)
    with Not_found ->
          match replace_chain replace m ref with
          | T -> T
          | F -> F
          | N(a,b) -> let res = bdd_of (replace_bdd a) (replace_bdd b)
                      in
                      Hashtbl.add visited (ref m) res;
                      res
  in
  replace_bdd m

let bdd_first_come_heuristic bdds _ =
  Bddset.fold (fun e a -> begin match e, a with
      | elt, (F, _) -> (elt, F)
      | elt, (a, F) -> (a, elt)
      | _, acc -> acc end
    ) bdds (F,F)
  
let bdd_merge_value_first_bdd_heuristic bdds nb_paths_to =
  let elt = Bddset.choose bdds in
  let nb_paths_to_elt = Hashtbl.find nb_paths_to (ref elt) in
  let card_elt = cardinal elt in
  let new_blss = Bddset.remove elt bdds in
  fst (Bddset.fold (fun elt2 (best, best_value) ->
                    (* We compute the merge value as defined in my report *)
                    let cardinal_two = cardinal (intersection elt elt2) in
                    let current_value = B.add_big_int (B.mult_big_int nb_paths_to_elt (B.sub_big_int (cardinal elt2) (cardinal_two))) (B.mult_big_int (Hashtbl.find nb_paths_to (ref elt2)) (B.sub_big_int (card_elt) (cardinal_two))) in
                    if current_value < best_value || best_value = B.zero_big_int then ((elt, elt2), current_value) else (best, best_value)
                  ) new_blss ((F, F), B.zero_big_int))
  
let bdd_merge_value_heuristic bdds nb_paths_to =
  let rec aux bdds (trees, mv) =
    if mv = B.unit_big_int then (trees, mv) else begin
        (* the try is here to say that when the set is empty, stop searching *)
        try let elt = Bddset.choose bdds in
            let nb_paths_to_elt = Hashtbl.find nb_paths_to (ref elt) in
            let card_elt = cardinal elt in
            let new_blss = Bddset.remove elt bdds in
            aux new_blss (Bddset.fold (fun elt2 (best, best_value) ->
                              (* We compute the merge value as defined in my report *)
                              let cardinal_two = cardinal (intersection elt elt2) in
                              let current_value = B.add_big_int (B.mult_big_int nb_paths_to_elt (B.sub_big_int (cardinal elt2) (cardinal_two))) (B.mult_big_int (Hashtbl.find nb_paths_to (ref elt2)) (B.sub_big_int (card_elt) (cardinal_two))) in
                              if (current_value < best_value || best_value = B.zero_big_int) then ((elt, elt2), current_value) else (best, best_value)
                            ) new_blss (trees, mv))
        with Not_found -> (trees, mv)
      end
  in
  fst (aux bdds ((F, F), B.zero_big_int))
  
  
let limited_bdd_of_bitvectset bls width heuristic =
  (* takes as input a BDD and return a BDD of bounded width. The merge heuristic can be changed *)
  let nb_paths_to = Hashtbl.create 101 in
  Hashtbl.add nb_paths_to bls B.unit_big_int;
  let replacement = Hashtbl.create 101 in
  let hash_split = Hashtbl.create 101 in
  let rec reduce layer =
    match Bvsetset.cardinal layer > width with
    | false -> layer
    | true -> let s1, s2 = heuristic layer nb_paths_to in
              let s = Bvset.union s1 s2 in
              if Bvset.compare s s1 != 0 then (increase_value nb_paths_to s (Hashtbl.find nb_paths_to s1);
                                               Hashtbl.add replacement s1 s);
              if Bvset.compare s s2 != 0 then (increase_value nb_paths_to s (Hashtbl.find nb_paths_to s2);
                                               Hashtbl.add replacement s2 s);
              reduce (Bvsetset.add s (Bvsetset.remove s1 (Bvsetset.remove s2 layer)))
  in
  let rec compute_layer blsset = match Bvsetset.is_empty blsset, Bvsetset.exists (fun x -> Bvset.exists (fun y -> y != []) x) blsset with
    | true, _ | _, false -> ()
    | _ ->
       let new_layer = Bvsetset.fold (fun t acc ->
                           let (zero, one) = split_zero_one_bvset t in
                           Hashtbl.add hash_split t (zero, one);
                           match Bvset.is_empty zero, Bvset.is_empty one with
                           | true, true -> acc
                           | true, false -> increase_value nb_paths_to one (Hashtbl.find nb_paths_to t);
                                            Bvsetset.add one acc
                           | false, true -> increase_value nb_paths_to zero (Hashtbl.find nb_paths_to t);
                                            Bvsetset.add zero acc
                           | false, false -> increase_value nb_paths_to one (Hashtbl.find nb_paths_to t);
                                             increase_value nb_paths_to zero (Hashtbl.find nb_paths_to t);
                                             Bvsetset.add zero (Bvsetset.add one acc)
                         ) blsset Bvsetset.empty in
       compute_layer (reduce new_layer)
  in
  compute_layer (Bvsetset.add bls (Bvsetset.empty));
  let already_computed = Hashtbl.create 101 in
  let rec generate_bdd blset =
    try Hashtbl.find already_computed blset
    with Not_found -> 
          match Bvset.is_empty blset with
          | true -> Hashtbl.add already_computed blset F;F
          | false ->
             match Bvset.exists (fun x -> x != []) blset with
             | true ->
                let (zero, one) = Hashtbl.find hash_split blset in (*split_zero_one blset in *)
                let nextone = bdd_of (generate_bdd (replace_chain replacement zero (fun x -> x))) (generate_bdd (replace_chain replacement one (fun x -> x))) in
                Hashtbl.add already_computed blset nextone;
                nextone
             | false -> Hashtbl.add already_computed blset T;T
  in
  generate_bdd bls

let first_come_heuristic blss _ =
  Bvsetset.fold (fun e a -> begin match e, a with
      | elt, acc when Bvset.is_empty elt-> acc
      | elt, (a, _) when Bvset.is_empty a -> (elt, Bvset.empty)
      | elt, (a, b) when Bvset.is_empty b -> (a, elt)
      | _, acc -> acc end
    ) blss (Bvset.empty, Bvset.empty)

let find hash key =
  Hashtbl.fold (fun k v acc ->
      if Bvset.compare k key = 0 then v else acc
    ) hash (-1)
  
let merge_value_heuristic blss nb_paths_to =
  let rec aux blss (trees, mv) =
    try let elt = Bvsetset.choose blss in
        let nb_paths_to_elt = find nb_paths_to elt in
        let new_blss = Bvsetset.remove elt blss in
        aux new_blss (Bvsetset.fold (fun elt2 (best, best_value) ->
                          (* We compute the merge value as defined in my report *)
                          let current_value = nb_paths_to_elt*(Bvset.cardinal (Bvset.diff elt2 elt)) + (find nb_paths_to elt2)*(Bvset.cardinal (Bvset.diff elt elt2)) in
                          if current_value < best_value then ((elt, elt2), current_value) else (best, best_value)
                        ) new_blss (trees, mv))
    with Not_found -> (trees,mv)
  in
  fst (aux blss ((Bvset.empty, Bvset.empty),max_int))

let extract_depth_k m wanted_depth =
  (* give the bddset of all the bdds at depth k in m, that are now a chain of N(a,a), and the bdd (to have it of the good depth *)
  let visited = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find visited (ref m);
    with Not_found -> 
      let res = 
        match depth m = wanted_depth, m with
        | true, _ -> Bddset.singleton m
        | false, T | false, F -> failwith "extract_depth_k: The wanted depth has not been found in the bdd"
        | false, N(a,b) -> Bddset.map (fun x -> bdd_of x x) (Bddset.union (aux a) (aux b))
      in 
      Hashtbl.add visited (ref m) res;
      res
  in
  aux m

let same_mod_propagator x x' k =
  (* Propagator for constraint x \congr x' [2^k] *)
  (multiple_mdd_consistency x (extract_depth_k x' k), multiple_mdd_consistency x' (extract_depth_k x k))

let cst_mod_propagator x c k =
  (* Propagator for constraint x mod 2^k = c with c a constant *)
  mdd_consistency x (bdd_of_int c k (depth x))

    
let rec inter_with_union bdd bdds =
  (* Computes the intersection bdd \inter (\Bigunion_i bdds[i]) where bdds is a set of bdd *)
  match bdd with
  | F -> F
  | T -> if Bddset.is_empty bdds then F else T
  | N(a,b) ->
     let zero, one = Bddset.fold (fun elt (zeroacc, oneacc) ->
                         match elt with
                         | F -> (zeroacc, oneacc)
                         | T -> failwith "inter_with_union : not the same size"
                         | N(F,F) -> failwith "inter_with_union : N(F,F) should be equal to F"
                         | N(F,a) -> (zeroacc, Bddset.add a oneacc)
                         | N(a,F) -> (Bddset.add a zeroacc, oneacc)
                         | N(a,b) -> (Bddset.add a zeroacc, Bddset.add b oneacc)
                       ) bdds (Bddset.empty, Bddset.empty) in
     bdd_of (inter_with_union a zero) (inter_with_union b one)

     
(* choice is the merge choice (not the heuristic) for nodes inside the BDD when it becomes too wide *)     
let improved_consistency_multiple m m' width choice =
  (* replacement contains all the mappings from the ancient, not-merged, nodes to the new merged nodes *)
  let replacement = Hashtbl.create 101 in
  let add_to_hash hash bdd set elt =
    (* useful function to add a set to a hashtbl in a hashtbl *)
    Hashtbl.add hash (ref bdd) (try Bddsmap.add set elt (Hashtbl.find hash (ref bdd))
                                with Not_found -> Bddsmap.singleton set elt)
  in
  let split_zero_one bdds =
    (* Take a bddset as input and return two bdds: one with all the 0-subtrees, and the other with all the 1-subtrees *) 
    Bddset.fold (fun elt (zeroacc, oneacc) ->
        match elt with
        | T -> failwith "split_zero_one_improved_cons_mult: not the same size"
        | F -> (zeroacc, oneacc)
        | N(F,F) -> failwith "inter_with_union : N(F,F) should be equal to F"
        | N(F,c) -> (zeroacc, Bddset.add c oneacc)
        | N(c,F) -> (Bddset.add c zeroacc, oneacc)
        | N(c,d) -> (Bddset.add c zeroacc, Bddset.add d oneacc)
      ) bdds (Bddset.empty, Bddset.empty)
  in
  let rec reduce bddbsset =
    (* take a layer as input, and return a reduced layer (with width smaller than said), and update the replacement hashtbl *)
    match Bddbddsset.cardinal bddbsset > width with
    | false -> bddbsset
    | true -> let s1, s2 = choice bddbsset in
              if fst s1 != fst s2 then failwith "the choice returned two nodes that don't come from the same node";
              let merge_union = Bddset.union (snd s1) (snd s2) in
              add_to_hash replacement (fst s1) (snd s1) merge_union;
              add_to_hash replacement (fst s2) (snd s2) merge_union;              
              reduce (Bddbddsset.add (fst s1, merge_union) (Bddbddsset.remove s1 (Bddbddsset.remove s2 bddbsset)))
  in
  let rec compute_layer bddbss =
    (* Will deal with each layer one by one *)
    let new_layer = Bddbddsset.fold (fun (m, bdds) acc ->
                        match m with
                        | T | F -> acc
                        | N(F,F) -> failwith "NFF should not happen because it is reduced"
                        | N(F,a) ->
                           let _, one = split_zero_one bdds in
                           Bddbddsset.add (a, one) acc
                        | N(a,F) -> 
                           let zero, _ = split_zero_one bdds in
                           Bddbddsset.add (a, zero) acc
                        | N(a,b) ->
                           let zero, one =  split_zero_one bdds in
                           Bddbddsset.add (a,zero) (Bddbddsset.add (b,one) acc)
                      ) bddbss Bddbddsset.empty
    in
    if Bddbddsset.is_empty new_layer then () else compute_layer (reduce new_layer)
  in
  let rec replace_chain_set (bdd, bdds) =
    (* Find the new bdd to use (aux function) *)
    try let bdd_map = Hashtbl.find replacement (ref bdd) in
        try let res = (bdd, Bddsmap.find bdds bdd_map) in
            if Bddset.compare (snd res) bdds = 0 then (bdd, bdds) else replace_chain_set res
        with Not_found -> (bdd, bdds)
    with Not_found -> (bdd, bdds)
  in
  let computed = Hashtbl.create 101 in
  let rec generate_new_bdd bdd bdds =
    (*print_endline (string_of_int (Hashtbl.length computed));*)
    try Bddsmap.find bdds (Hashtbl.find computed (ref bdd))
    with Not_found ->
          (* Will generate the new bdd *)
          let (new_bdd, new_bdds) = replace_chain_set (bdd, bdds) in
          try Bddsmap.find bdds (Hashtbl.find computed (ref bdd))
          with Not_found -> 
            let res = match new_bdd, Bddset.is_empty bdds with
              | F, _ | _, true -> F
              | T, false -> T (*if Bddset.compare (Bddset.singleton T) new_bdds = 0 then T else (print_endline ("test");failwith ("not the same depth while generating new bdd"^(string_of_bddset bdds)))*)
              | N(a,b), false -> 
                 let zero, one = split_zero_one new_bdds in
                 bdd_of (generate_new_bdd a zero) (generate_new_bdd b one)
            in
            add_to_hash computed bdd bdds res;
            res
  in
  compute_layer (Bddbddsset.singleton (m, m'));
  generate_new_bdd m m'
  
let improved_consistency m m' width choice =
  improved_consistency_multiple m (Bddset.singleton m') width choice


let random_heuristic_improved_consistency bddbss =
  (*print_endline "heuristic";*)
  let bdd_exists = Hashtbl.create 101 in
  Bddbddsset.fold (fun (bdd, bdds) ((bddacc, bddsacc), acc) ->
      (*print_endline (string_of_bdd bdd);*)
      match Bddset.is_empty bddsacc with
      | false -> (bddacc, bddsacc), acc
      | true -> try (bdd,Hashtbl.find bdd_exists (ref bdd)), (bdd, bdds)
                 with Not_found -> Hashtbl.add bdd_exists (ref bdd) bdds; (bddacc, bddsacc), acc
    ) bddbss ((F, Bddset.empty), (F, Bddset.empty))










    

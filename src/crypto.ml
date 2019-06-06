open Useful
open Bdd

(*******************************************************)
(* Computation of the S-box functions, arrays and BDDs *)
   
let sbox_hex =
  (* The first dimension of the array are the 4 higher bits of the input, the second dimension are the 4 lower bits *)
  [|[| "63"; "7C"; "77";"7B";"F2";"6B";"6F";"C5";"30";"01";"67";"2B";"FE";"D7";"AB";"76"|];
    [| "CA"; "82"; "C9";"7D";"FA";"59";"47";"F0";"AD";"D4";"A2";"AF";"9C";"A4";"72";"C0"|];
    [| "B7";"FD";"93";"26";"36";"3F";"F7";"CC";"34";"A5";"E5";"F1";"71";"D8";"31";"15"|];
    [| "04";"C7";"23";"C3";"18";"96";"05";"9A";"07";"12";"80";"E2";"EB";"27";"B2";"75"|];
    [| "09";"83";"2C";"1A";"1B";"6E";"5A";"A0";"52";"3B";"D6";"B3";"29";"E3";"2F";"84"|];
    [| "53";"D1";"00";"ED";"20";"FC";"B1";"5B";"6A";"CB";"BE";"39";"4A";"4C";"58";"CF"|];
    [| "D0";"EF";"AA";"FB";"43";"4D";"33";"85";"45";"F9";"02";"7F";"50";"3C";"9F";"A8"|];
    [| "51";"A3";"40";"8F";"92";"9D";"38";"F5";"BC";"B6";"DA";"21";"10";"FF";"F3";"D2"|];
    [| "CD";"0C";"13";"EC";"5F";"97";"44";"17";"C4";"A7";"7E";"3D";"64";"5D";"19";"73"|];
    [| "60";"81";"4F";"DC";"22";"2A";"90";"88";"46";"EE";"B8";"14";"DE";"5E";"0B";"DB"|];
    [| "E0";"32";"3A";"0A";"49";"06";"24";"5C";"C2";"D3";"AC";"62";"91";"95";"E4";"79"|];
    [| "E7";"C8";"37";"6D";"8D";"D5";"4E";"A9";"6C";"56";"F4";"EA";"65";"7A";"AE";"08"|];
    [| "BA";"78";"25";"2E";"1C";"A6";"B4";"C6";"E8";"DD";"74";"1F";"4B";"BD";"8B";"8A"|];
    [| "70";"3E";"B5";"66";"48";"03";"F6";"0E";"61";"35";"57";"B9";"86";"C1";"1D";"9E"|];
    [| "E1";"F8";"98";"11";"69";"D9";"8E";"94";"9B";"1E";"87";"E9";"CE";"55";"28";"DF"|];
    [| "8C";"A1";"89";"0D";"BF";"E6";"42";"68";"41";"99";"2D";"0F";"B0";"54";"BB";"16"|]|]
         
module Chmap = Map.Make(Char)
             
let int_of_hex =
  (* Conversion function from hex character to int *)
  let conversion = Chmap.add 'A' 10 (Chmap.add 'B' 11 (Chmap.add 'C' 12 (Chmap.add 'D' 13 (Chmap.add 'E' 14 (Chmap.add 'F' 15 Chmap.empty))))) in
  let rec aux n map = match n with
    | -1 -> map
    | _ -> aux (n-1) (Chmap.add (string_of_int n).[0] n map)
  in aux 9 conversion

let int_of_hexstring s =
  (* Return the integer represented by a hexadecimal string *)
  let res = ref 0 in
  for i=0 to String.length s - 1 do
    res := try Chmap.find s.[i] int_of_hex + 16 * !res with Not_found -> print_string (Char.escaped s.[i]); failwith "test";
  done;
  !res
  
let sbox =
  (* The array of the outputs of the S-box in integers *)
  Array.init 256 (fun i -> int_of_hexstring sbox_hex.(i lsr 4).(i land 15))
  
let inverse_sbox =
  (* The inverse function of the S-box, computed using the previous array *)
  let inverse = Array.make 256 0 in
  Array.iteri (fun i elt -> inverse.(elt) <- i) sbox;
  inverse
      
let sbox_fun x =
  (* The S-box as a function *)
  sbox.(x)

let array_diff_sbox_outputs =
  (* The array giving for each differtial byte the set of possible outputs *)
  let res = Array.make 256 Intset.empty in
  for i=0 to 255 do
    for j=0 to 255 do
      res.(i lxor j) <- Intset.add (sbox.(i) lxor sbox.(j)) res.(i lxor j)
    done
  done;
  res
  
let input_output_bdd output_fun =
  (* return a bdd where the values are X \concat Y where Y = output_fun(X) *)
  let rec aux n set =
    let rec aux2 m set2 = match m with
      | -1 -> set2
      | _ -> let res = (((n lxor m) lsl 8) lor ((output_fun.(n)) lxor (output_fun.(m)))) in
             aux2 (m-1) (Bvset.add (bitvect_of_int res 16) set2)
    in
    match n with
    | -1 -> set
    | _ -> aux (n-1) (aux2 255 set)
  in
  bdd_of_bitvectset (aux 255 Bvset.empty)

let input_output_sbox =
  (* The BDD of the S-box *)
  try get_from_file "src/saved_bdd/input_output_sbox.bdd"
  with _ -> let res = input_output_bdd sbox in
            save_to_file res "src/saved_bdd/input_output_sbox.bdd";
            res
            
let input_output_inverse_sbox = 
  (* The BDD of the inverse S-box *)
  try get_from_file "src/saved_bdd/input_output_inverse_sbox.bdd"
  with _ -> let res = input_output_bdd inverse_sbox in
            save_to_file res "src/saved_bdd/input_output_inverse_sbox.bdd";
            res

                              
let probaS =
  (* Logarithm of the probability that inputing a in the differential s-box gives b *)
  let computed = Hashtbl.create 101 in
  let aux a b =
    try Hashtbl.find computed (a,b)
    with Not_found ->
          let res = 
            let count = ref (-16) in
            for i=0 to 255 do
              if sbox.(i) lxor sbox.(i lxor a) = b then incr count
            done;
            !count/2 in
          Hashtbl.add computed (a,b) res;
          res in
  aux
            
let input_output_sbox_proba =
  (* return the bdd representing the S-box where the probability is 2^-6 *)
  try get_from_file "src/saved_bdd/input_output_sbox_proba.bdd"
  with _ ->
    let res =
      let rec aux n set =
        let rec aux2 m set2 =
          match m with
          | -1 -> set2
          | _ -> let res = (n lsl 8) lor m in
                 aux2 (m-1) (if probaS n m = -6 then Bvset.add (bitvect_of_int res 16) set2 else set2)
        in
        match n with
        | -1 -> set
        | _ -> aux (n-1) (aux2 255 set)
      in
      bdd_of_bitvectset (aux 255 Bvset.empty) in
    save_to_file res "src/saved_bdd/input_output_sbox_proba.bdd";
    res
    
let input_output_inverse_sbox_proba = 
  (* return the bdd representing the inverse S-box where the probability is 2^-6 *)
  try get_from_file "src/saved_bdd/input_output_inverse_sbox_proba.bdd"
  with _ ->
    let res =
      let rec aux n set =
        let rec aux2 m set2 =
          match m with
          | -1 -> set2
          | _ -> let res = (m lsl 8) lor n in
                 aux2 (m-1) (if probaS n m >= -6 then Bvset.add (bitvect_of_int res 16) set2 else set2)
        in
        match n with
        | -1 -> set
        | _ -> aux (n-1) (aux2 255 set)
      in
      bdd_of_bitvectset (aux 255 Bvset.empty) in
    save_to_file res "src/saved_bdd/input_output_inverse_sbox_proba.bdd";
    res



(******************************************)
(* Computation of the Mix column function *)
    
let add_zero_end =
  (* equivalent to the concatenation of the bdd and N(T,F) but a little little faster *)
  let last = bdd_of T F in
  let computed = Hashtbl.create 101 in
  let rec aux m =
    try Hashtbl.find computed (ref m)
    with Not_found ->
          let res = match m with
            | T -> last
            | F -> F
            | N(a,b) -> bdd_of (aux a) (aux b)
          in
          Hashtbl.add computed (ref m) res;
          res
  in aux


let gl_double_int x =
  (* Double the byte as defined by the MC operations *)
  if x land 128 = 0 then (x lsl 1) land 255 else ((x lsl 1) land 255) lxor 27

let gl_triple_int x =
  (* Triple the byte as defined by the MC operations *)
  gl_double_int x lxor x
  
let mix_column_int x0 x1 x2 x3 =
  (* mix column on integers *)
  (gl_double_int x0) lxor (gl_triple_int x1) lxor x2 lxor x3,
  (gl_double_int x1) lxor (gl_triple_int x2) lxor x3 lxor x0,
  (gl_double_int x2) lxor (gl_triple_int x3) lxor x0 lxor x1,
  (gl_double_int x3) lxor (gl_triple_int x0) lxor x1 lxor x2

(* We generate some BDDs to cache some computations *)
(* The BDDs that are generated are the ones where three out of four of the inputs of the MC is equal to zero. The other input is equal to anything in [0,255], like this we can see all the outputs, and do a propagation using the generated BDD (instead of computing the MC on BDDs *)
let single_zero_mc =
  let res = [|F;F;F;F|] in
  for i = 0 to 3 do
    res.(i) <-
      try get_from_file ("src/saved_bdd/single_zero_input_"^(string_of_int i)^".bdd")
      with _ ->
        let rec aux n acc =
          match n with
          | -1 -> acc
          | _ -> let x0,x1,x2,x3 = (if i = 0 then n else 0), (if i = 1 then n else 0), (if i = 2 then n else 0), (if i = 3 then n else 0) in
                 let y0,y1,y2,y3 = mix_column_int x0 x1 x2 x3 in
                 aux (n-1) (union acc (concatenate_bdd (bdd_of_int n 8 8) (concatenate_bdd (bdd_of_int y0 8 8) (concatenate_bdd (bdd_of_int y1 8 8) (concatenate_bdd (bdd_of_int y2 8 8) (bdd_of_int y3 8 8)))))) in
        let computed = aux 255 F in
        save_to_file computed ("src/saved_bdd/single_zero_input_"^(string_of_int i)^".bdd");
        computed
  done;
  res

(* For the two next functions the hashtable is maybe not necessary *)
let gl_double =
  let computed = Hashtbl.create 101 in
  let aux m =
    try Hashtbl.find computed (ref m)
    with Not_found ->
          let res = match m with
            | T | F -> failwith "lsl:the domain is empty"
            | N(a,b) -> union (add_zero_end a) (bdd_xor (add_zero_end b) (bdd_of_int 27 8 8)) in
          Hashtbl.add computed (ref m) res;
          res in
  aux

let mix_column_bdd =
  let computed = Hashtbl.create 101 in
  let aux x0 x1 x2 x3 =
    try Hashtbl.find computed (ref x0,ref x1,ref x2,ref x3)
    with Not_found ->
      let double_array = Array.map (fun x -> gl_double x) [|x0; x1; x2; x3|] in
      (* These two xor functions are used twice, so we compute less by computing them before *)
      let xor_01 = bdd_xor x0 x1 in
      let xor_23 = bdd_xor x2 x3 in
      let res =
        bdd_xor (double_array.(0)) (bdd_xor (double_array.(1)) (bdd_xor x1 xor_23)),
        bdd_xor (double_array.(1)) (bdd_xor (double_array.(2)) (bdd_xor x0 xor_23)),
        bdd_xor (double_array.(2)) (bdd_xor (double_array.(3)) (bdd_xor x3 xor_01)),
        bdd_xor (double_array.(3)) (bdd_xor (double_array.(0)) (bdd_xor x2 xor_01)) in
      Hashtbl.add computed (ref x0,ref x1,ref x2,ref x3) res;
      res in
  aux

(* For these functions, we assume that the multiplication by eight is already done *)
let gl_13 powers =
  bdd_xor powers.(0) powers.(2)
                    
let gl_14 powers =
  bdd_xor powers.(1) powers.(2)
  
let inverse_mix_column_bdd =
  let computed = Hashtbl.create 101 in
  let aux y0 y1 y2 y3 =
    try Hashtbl.find computed (ref y0,ref y1,ref y2,ref y3)
    with Not_found ->
      let powers = Array.make_matrix 4 4 F in
      powers.(0).(0) <- y0;
      powers.(1).(0) <- y1;
      powers.(2).(0) <- y2;
      powers.(3).(0) <- y3;
      for i=1 to 3 do
        for j=0 to 3 do
          powers.(j).(i) <- gl_double (powers.(j).(i-1));
        done
      done;
      let all_eight = bdd_xor powers.(0).(3) (bdd_xor powers.(1).(3) (bdd_xor powers.(2).(3) powers.(3).(3))) in
      let xor_02 = bdd_xor y0 y2 in
      let xor_13 = bdd_xor y1 y3 in
      let res = bdd_xor all_eight (bdd_xor xor_13 (bdd_xor (gl_14 powers.(0)) (bdd_xor powers.(1).(1) (gl_13 powers.(2))))),
                bdd_xor all_eight (bdd_xor xor_02 (bdd_xor (gl_14 powers.(1)) (bdd_xor powers.(2).(1) (gl_13 powers.(3))))),
                bdd_xor all_eight (bdd_xor xor_13 (bdd_xor (gl_14 powers.(2)) (bdd_xor powers.(3).(1) (gl_13 powers.(0))))),
                bdd_xor all_eight (bdd_xor xor_02 (bdd_xor (gl_14 powers.(3)) (bdd_xor powers.(0).(1) (gl_13 powers.(1))))) in
      Hashtbl.add computed (ref y0,ref y1,ref y2,ref y3) res;
      res in
  aux

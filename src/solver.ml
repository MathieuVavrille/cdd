open Crypto
open Useful
open Bdd
open Cstrbdd

type var = X of int * int * int
         | SX of int * int * int
         | K of int * int * int
         | SK of int * int (* It is always on the third column *)
         | Z of int * int * int

let do_limited = true
                   
let improved_consistency a b _ _ = (if do_limited then mdd_consistency else intersection) a b

let improved_consistency_multiple a b _ _ = (if do_limited then multiple_mdd_consistency else inter_of_union) a b
                    
(* A comparison function between variables, simply to have a total order between them *)
let compare_var v1 v2 = match v1, v2 with
  | X(i1,i2,i3), X(j1,j2,j3)
    | SX(i1,i2,i3), SX(j1,j2,j3)
    | K(i1,i2,i3), K(j1,j2,j3)
    | Z(i1,i2,i3), Z(j1,j2,j3) -> list_compare Pervasives.compare [i1;i2;i3] [j1;j2;j3]
  | SK(i1,i2), SK(j1,j2) -> list_compare Pervasives.compare [i1;i2] [j1;j2]
  | X _, _ -> 1
  | _, X _ -> -1
  | SX _, _ -> 1
  | _, SX _ -> -1
  | K _, _ -> 1
  | _, K _ -> -1
  | SK _, _ -> 1
  | _, SK _ -> -1

module Store = Map.Make(struct type t = var let compare = compare_var end)

module Varset = Set.Make(struct type t = var let compare = compare_var end)

let string_of_var v = match v with
  | X(a,b,c) -> "x_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
  | SX(a,b,c) -> "sx_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
  | K(a,b,c) -> "k_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
  | SK(a,b) -> "sk_"^(string_of_int a)^"_"^(string_of_int b)^"_3"
  | Z(a,b,c) -> "z_"^(string_of_int a)^"_"^(string_of_int b)^"_"^(string_of_int c)
             
(* The constraint type: all the active S-boxes are represented in Active SB (the other ones are equal to zero) *)
type cstr = Xor of var * var * var
          | Mc of var * var * var * var * var * var * var * var
          | Not_zero of var
          | ActiveSB of (var * var) list * int ref
          | Iscst of var * int
          | Le of var * var (* var <= var *)

let cstr_compare c1 c2 = match c1, c2 with
  (* When the constraint have the same type, we compare the arguments *)
  | Xor(a1,b1,c1), Xor(a2,b2,c2) -> list_compare compare_var [a1;b1;c1] [a2;b2;c2]
  | Mc(a1,b1,c1,d1,e1,f1,g1,h1) , Mc(a2,b2,c2,d2,e2,f2,g2,h2) -> list_compare compare_var [a1;b1;c1;d1;e1;f1;g1;h1] [a2;b2;c2;d2;e2;f2;g2;h2]
  | Not_zero(a1), Not_zero(a2) -> compare_var a1 a2
  | ActiveSB(l1,b1), ActiveSB(l2,b2) -> begin match list_compare (fun (a1,b1) (a2,b2) -> match compare_var a1 a2 with
                                                                                         | 0 -> compare_var b1 b2
                                                                                         | n -> n) l1 l2 with
                                        | 0 -> Pervasives.compare !b1 !b2
                                        | n -> n
                                        end
  | Iscst(s1,i1), Iscst(s2,i2) -> begin match Pervasives.compare s1 s2 with
                                  | 0 -> Pervasives.compare i1 i2
                                  | n -> n
                                  end
  | Le(s1,i1), Le(s2,i2) -> begin match Pervasives.compare s1 s2 with
                            | 0 -> Pervasives.compare i1 i2
                            | n -> n
                            end
  (* Here we order when the constraints have different types *)
  | Iscst _, _ -> 1
  | _, Iscst _ -> -1
  | Not_zero _, _ -> 1
  | _, Not_zero _ -> -1
  | Xor _, _ -> 1
  | _, Xor _ -> -1
  | Le _, _ -> 1
  | _, Le _ -> -1
  | Mc _, _ -> 1
  | _, Mc _ -> -1

module Cstrset = Set.Make(struct type t = cstr let compare = cstr_compare end)

module Cstrmap = Map.Make(struct type t = cstr let compare = cstr_compare end)
                                     
(* A conversion function *)    
let string_of_cstr c = match c with
  | Xor(a,b,c) -> "XOR("^(string_of_var a)^","^(string_of_var b)^","^(string_of_var c)^")"
  | Mc(a,b,c,d,e,f,g,h) -> "MC("^(string_of_var a)^","^(string_of_var b)^","^(string_of_var c)^","^(string_of_var d)^","^(string_of_var e)^","^(string_of_var f)^","^(string_of_var g)^","^(string_of_var h)^")"
  | Not_zero(a) -> "NOT_ZERO("^(string_of_var a)^")"
  | ActiveSB(l, b) -> "ACTIVESB("^(string_of_list (fun (x,y) -> (string_of_var x)^","^(string_of_var y)) l)^","^(string_of_int !b)^")"
  | Iscst(s,i) -> "Is_cst("^(string_of_var s)^","^(string_of_int i)^")"
  | Le(a,b) -> string_of_var a^"<="^string_of_var b
                
(* Returns all the variables that have been modified *)
let get_modified = List.fold_left (fun acc (x,bdd,res) -> if bdd == res then acc else x::acc) []

let time_xor = ref 0.
let time_xor_computation = ref 0.
let time_xor_computation_give_depth = ref 0.
let time_xor_computation_xor = ref 0.
let time_xor_consistency = ref 0.
let cstr_xor_bdd =
  let rec aux n m acc = match n,m with
    | -1, _ -> acc
    | _, -1 -> aux (n-1) 255 acc
    | _, _ -> aux n (m-1) ((n*65536 + m*256 + (n lxor m))::acc)
  in
  let xor_list = aux 255 255 [] in
  bdd_of_intlist xor_list 24
let propagator_xor_new a b c store (cstrbdd,w_cstr_bdd) =
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let bddc,wc = Store.find c store in
  let deptha, depthb, depthc = depth bdda, depth bddb, depth bddc in
  let t = Sys.time () in
  let temp = concatenate_bdd (cutted_bdd 8 bdda) (concatenate_bdd (cutted_bdd 8 bddb) (cutted_bdd 8 bddc)) in
  let propagated_cstrbdd = improved_consistency cstrbdd temp w_cstr_bdd random_heuristic_improved_consistency in
  time_xor_consistency := !time_xor_consistency +. Sys.time () -. t;
  if propagated_cstrbdd == F then Store.add (X(-1,-1,-1)) (F,1) store, (cstrbdd,w_cstr_bdd), [X(-1,-1,-1)]
  else begin
      let t2 = Sys.time () in
      let cons_a = give_depth deptha (cutted_bdd 8 propagated_cstrbdd) in
      let cons_b = possible_outputs complete8 (give_depth (8+depthb) (cutted_bdd 16 propagated_cstrbdd)) in
      let cons_c = possible_outputs complete16 (give_depth (16+depthc) propagated_cstrbdd) in
      let t = Sys.time () in
      time_xor_computation := !time_xor_computation +. t -. t2;
      let res_a = improved_consistency bdda cons_a wa random_heuristic_improved_consistency in 
      let res_b = improved_consistency_multiple bddb cons_b wb random_heuristic_improved_consistency in
      let res_c = improved_consistency_multiple bddc cons_c wc random_heuristic_improved_consistency in
      time_xor_consistency := !time_xor_consistency +. Sys.time () -. t;
      Store.add a (res_a,wa) (Store.add b (res_b,wb) (Store.add c (res_c,wc) store)),
      (propagated_cstrbdd,w_cstr_bdd),
      get_modified [a,bdda,res_a;b,bddb,res_b;c,bddc,res_c] end

let propagator_xor a b c store cstrbdd =
  let t = Sys.time () in
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let bddc,wc = Store.find c store in
  let deptha, depthb, depthc = depth bdda, depth bddb, depth bddc in
  let t2 = Sys.time () in
  let give_ab = give_depth deptha bddb in
  let give_ac = give_depth deptha bddc in
  let give_ba = give_depth depthb bdda in
  let give_bc = give_depth depthb bddc in
  let give_ca = give_depth depthc bdda in
  let give_cb = give_depth depthc bddb in
  let t3 = Sys.time () in
  time_xor_computation_give_depth := !time_xor_computation_give_depth +. t3 -. t2;
  let cons_a = bdd_xor give_ab give_ac in
  let cons_b = bdd_xor give_ba give_bc in
  let cons_c = bdd_xor give_ca give_cb in
  time_xor_computation_xor := !time_xor_computation_xor +. Sys.time () -. t3;
  time_xor_computation := !time_xor_computation +. Sys.time () -. t2;
  let t2 = Sys.time () in
  let res_a = if subset bdda cons_a then bdda else improved_consistency bdda cons_a wa random_heuristic_improved_consistency in
  let res_b = if subset bddb cons_b then bddb else improved_consistency bddb cons_b wb random_heuristic_improved_consistency in
  let res_c = if subset bddc cons_c then bddc else improved_consistency bddc cons_c wc random_heuristic_improved_consistency in
  time_xor_consistency := !time_xor_consistency +. Sys.time () -. t2;
  time_xor := !time_xor +. Sys.time () -. t;
  Store.add a (res_a,wa) (Store.add b (res_b,wb) (Store.add c (res_c,wc) store)),
  cstrbdd,
  get_modified [a,bdda,res_a;b,bddb,res_b;c,bddc,res_c]

  
let time_mc = ref 0.
let time_fun_mc = ref 0.
let time_fun_mc_normal = ref 0.
let time_fun_mc_inverse = ref 0.
let time_mc_consistency = ref 0.
let time_mc_cons_single = ref 0.
let propagator_mc a b c d e f g h store (cstrbdd,cstrbdd_width) first = (* TODO remove first, for debug purpose *)
  let t = Sys.time() in
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let bddc,wc = Store.find c store in
  let bddd,wd = Store.find d store in
  let bdde,we = Store.find e store in
  let bddf,wf = Store.find f store in
  let bddg,wg = Store.find g store in
  let bddh,wh = Store.find h store in
  let do_improved = (* Computes the index of the bdd that is not equal zero if there is a unique one, otherwise return -1*)
    if bdda != zero_bdd16 && bddb == zero_bdd8 && bddc == zero_bdd8 && bddd == zero_bdd8 then 0
    else
      if bddb != zero_bdd16 && bdda == zero_bdd8 && bddc == zero_bdd8 && bddd == zero_bdd8 then 1
      else
        if bddc != zero_bdd16 && bdda == zero_bdd8 && bddb == zero_bdd8 && bddd == zero_bdd8 then 2
        else
          if bddd != zero_bdd16 && bdda == zero_bdd8 && bddb == zero_bdd8 && bddc == zero_bdd8 then 3
          else -1 in
  if do_improved != -1 && first then begin (* When only one input is not equal to zero we can improve the consistency *)
      let bigtest = (concatenate_bdd (cutted_bdd 8 [|bdda;bddb;bddc;bddd|].(do_improved)) (concatenate_bdd bdde (concatenate_bdd bddf (concatenate_bdd bddg bddh)))) in
      let propagated_cstrbdd = improved_consistency (if cstrbdd == F then single_zero_mc.(do_improved) else cstrbdd) bigtest cstrbdd_width random_heuristic_improved_consistency  in
      if propagated_cstrbdd == F then Store.add (X(-1,-1,-1)) (F, 1) store, (cstrbdd,0), [X(-1,-1,-1)]
      else begin
          let new_input = give_depth (depth [|bdda;bddb;bddc;bddd|].(do_improved)) (cutted_bdd 8 propagated_cstrbdd) in
          let res_a = if do_improved = 0 then improved_consistency bdda new_input wa random_heuristic_improved_consistency else bdda in
          let res_b = if do_improved = 1 then improved_consistency bddb new_input wb random_heuristic_improved_consistency else bddb in
          let res_c = if do_improved = 2 then improved_consistency bddc new_input wc random_heuristic_improved_consistency else bddc in
          let res_d = if do_improved = 3 then improved_consistency bddd new_input wd random_heuristic_improved_consistency else bddd in
          let res_e = improved_consistency_multiple bdde (possible_outputs complete8 (cutted_bdd 16 propagated_cstrbdd)) wf random_heuristic_improved_consistency in
          let res_f = improved_consistency_multiple bddf (possible_outputs complete16 (cutted_bdd 24 propagated_cstrbdd)) wf random_heuristic_improved_consistency in
          let res_g = improved_consistency_multiple bddg (possible_outputs (complete_bdd 24) (cutted_bdd 32 propagated_cstrbdd)) wg random_heuristic_improved_consistency in
          let res_h = improved_consistency_multiple bddh (possible_outputs (complete_bdd 32) propagated_cstrbdd) wh random_heuristic_improved_consistency in
          Store.add a (res_a,wa) (Store.add b (res_b,wb) (Store.add c (res_c,wc) (Store.add d (res_d,wd) (Store.add e (res_e,we) (Store.add f (res_f,wf) (Store.add g (res_g,wg) (Store.add h (res_h,wh) store))))))),
          (propagated_cstrbdd,cstrbdd_width),
          get_modified [a,bdda,res_a;b,bddb,res_b;c,bddc,res_c;d,bddd,res_d;e,bdde,res_e;f,bddf,res_f;g,bddg,res_g;h,bddh,res_h] end end

  else begin (* Case when there are more than one input not equal to zero (not optimized case) *)
      let t2 = Sys.time() in
      let cons_e, cons_f, cons_g, cons_h = mix_column_bdd (cutted_bdd 8 bdda) (cutted_bdd 8 bddb) (cutted_bdd 8 bddc) (cutted_bdd 8 bddd) in
      time_fun_mc := !time_fun_mc +. Sys.time () -. t2;
      time_fun_mc_normal := !time_fun_mc_normal +. Sys.time () -. t2;
      (*if do_improved != -1 then time_fun_mc := !time_fun_mc +. Sys.time () -. t2;*)
      let t3 = Sys.time () in
      let temp_res_e = improved_consistency (cutted_bdd 8 bdde) cons_e we random_heuristic_improved_consistency in
      let res_e = if temp_res_e != F then give_depth (depth bdde) temp_res_e else temp_res_e in
      let res_f = improved_consistency bddf cons_f wf random_heuristic_improved_consistency in
      let res_g = improved_consistency bddg cons_g wg random_heuristic_improved_consistency in
      let res_h = improved_consistency bddh cons_h wh random_heuristic_improved_consistency in
      time_mc_consistency := !time_mc_consistency +. Sys.time () -. t3;
      if res_e == F || res_f == F || res_g == F || res_h == F then Store.add (X(-1,-1,-1)) (F, 1) store, (cstrbdd, cstrbdd_width), [X(-1,-1,-1)]
      else begin
          let t2 = Sys.time() in
          let cons_a, cons_b, cons_c, cons_d = inverse_mix_column_bdd (cutted_bdd 8 res_e) res_f res_g res_h in (* I use the original bdds instead of the propagated ones because of the possibility of an empty bdd *)
          time_fun_mc := !time_fun_mc +. Sys.time () -. t2;
          time_fun_mc_inverse := !time_fun_mc_inverse +. Sys.time () -. t2;
          let t3 = Sys.time () in
          let res_a = if subset (cutted_bdd 8 bdda) cons_a then bdda else improved_consistency bdda (give_depth (depth bdda) cons_a) wa random_heuristic_improved_consistency in
          let res_b = if subset (cutted_bdd 8 bddb) cons_a then bddb else improved_consistency bddb (give_depth (depth bddb) cons_b) wb random_heuristic_improved_consistency in
          let res_c = if subset (cutted_bdd 8 bddc) cons_a then bddc else improved_consistency bddc (give_depth (depth bddc) cons_c) wc random_heuristic_improved_consistency in
          let res_d = if subset (cutted_bdd 8 bddd) cons_a then bddd else improved_consistency bddd (give_depth (depth bddd) cons_d) wd random_heuristic_improved_consistency in
          time_mc_consistency := !time_mc_consistency +. Sys.time () -. t3;
          time_mc := !time_mc +. Sys.time () -. t;
          Store.add a (res_a,wa) (Store.add b (res_b,wb) (Store.add c (res_c,wc) (Store.add d (res_d,wd) (Store.add e (res_e,we) (Store.add f (res_f,wf) (Store.add g (res_g,wg) (Store.add h (res_h,wh) store))))))),
          (cstrbdd,cstrbdd_width),
          get_modified [a,bdda,res_a;b,bddb,res_b;c,bddc,res_c;d,bddd,res_d;e,bdde,res_e;f,bddf,res_f;g,bddg,res_g;h,bddh,res_h] end end

  
let full_propagator_function inverse a b store =
  let bdda, wa = Store.find a store in
  let bddb, wb = Store.find b store in
  let new_out = improved_consistency bddb (concatenate_bdd complete8 (cutted_bdd 8 bdda)) wb random_heuristic_improved_consistency in
  if new_out != F then
      let res_b = if not (subset new_out inverse) then improved_consistency new_out inverse wb random_heuristic_improved_consistency else new_out in
      if res_b != F then begin
          let possible = possible_outputs complete8 res_b in
          let res_a = improved_consistency_multiple bdda possible wa random_heuristic_improved_consistency in
          Store.add a (res_a,wa) (Store.add b (res_b,wb) store), get_modified [a,bdda,res_a;b,bddb,res_b]
        end
      else
        Store.add (X(-1,-1,-1)) (F, 1) store, [X(-1,-1,-1)]
  else
    Store.add (X(-1,-1,-1)) (F, 1) store, [X(-1,-1,-1)]

let full_propagator_sb = full_propagator_function input_output_inverse_sbox

let full_propagator_psb = full_propagator_function input_output_inverse_sbox_proba
  
let propagator_function f inverse a b store =
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let res_b = improved_consistency_multiple bddb (possible_outputs bdda f) wb random_heuristic_improved_consistency in
  let res_a = improved_consistency_multiple bdda (possible_outputs bddb inverse) wa random_heuristic_improved_consistency in
  Store.add a (res_a,wa) (Store.add b (res_b,wb) store), get_modified [a,bdda,res_a;b,bddb,res_b]
  
(*let propagator_sb = propagator_function input_output_sbox input_output_inverse_sbox *)
                  
(*let propagator_psb = propagator_function input_output_sbox_proba input_output_inverse_sbox_proba*)

let test_propagator_function a b store =
  let bdda, wa = Store.find a store in
  let bddb, wb = Store.find b store in
  let new_out = improved_consistency bddb (concatenate_bdd complete8 bdda) wb random_heuristic_improved_consistency in
  if new_out != F then begin
      let possible = possible_outputs complete8 bddb in
      let res_a = improved_consistency_multiple bdda possible wa random_heuristic_improved_consistency in
      Store.add a (res_a,wa) (Store.add b (bddb,wb) store), get_modified [a,bdda,res_a;b,bddb,bddb]
    end
  else
    Store.add (X(-1,-1,-1)) (F, 1) store, [X(-1,-1,-1)]
                   
(* The constants are defined on one byte, this propagator is called only once in the initialization of the variable *)
let propagator_cst i a store cstrbdd =
  let bdda, wa = Store.find a store in
  let bddcst = bdd_of_int i 8 8 in
  try Store.add a (concatenate_bdd bddcst (Bddset.choose (possible_outputs bddcst bdda)), wa) store, cstrbdd, [a]
  with Not_found -> (* the input bdd does not contain the constant *)
    Store.add a (F,wa) store, cstrbdd, [a]
       
let propagator_not_zero a store cstrbdd =
  let bdda,wa = Store.find a store in
  let depth_a = depth bdda in
  let not_zero = give_depth depth_a not_zero_bdd8 in
  let res_a = improved_consistency bdda not_zero wa random_heuristic_improved_consistency in
  if res_a == bdda then store, cstrbdd, [] else Store.add a (res_a,wa) store, cstrbdd, [a]


let time_active_sb = ref 0.
let time_active_sb_not_cons = ref 0.
let time_active_sb_not_cons_int_of_bdd = ref 0.
let propagator_active_sb l b store cstrbdd = (* TODO Improve the propagator_active_sb with the cstrbdd *)
  let t = Sys.time () in
  let not_fixed, rest_bound =
    List.fold_left
      (fun (not_fixed_acc, rest_bound_acc) (var_in, var_out) ->
        try let t2 = Sys.time () in let cst_in, cst_out = int_of_bdd (cutted_bdd 8 (fst (Store.find var_in store))), int_of_bdd (cutted_bdd 8 (fst (Store.find var_out store))) in time_active_sb_not_cons_int_of_bdd := !time_active_sb_not_cons_int_of_bdd +. Sys.time () -. t2;(not_fixed_acc, rest_bound_acc - probaS cst_in cst_out)
        with Failure _ -> ((var_in, var_out)::not_fixed_acc, rest_bound_acc)
          (*let c_bdd = fst (Store.find var_out store) in
          (((var_in, var_out)::not_fixed_acc), rest_bound_acc + if is_empty (intersection c_bdd input_output_inverse_sbox_proba) then 1 else 0)*)
      ) ([], b) l in
  let current_bound = List.length not_fixed * -6 in
  let propag = if rest_bound >= current_bound then full_propagator_psb else full_propagator_sb in
  time_active_sb_not_cons := !time_active_sb_not_cons +. Sys.time () -. t;
  let res_store, res_vars = if current_bound >= rest_bound then
              List.fold_left
                (fun (new_store, modified_vars) (var_in, var_out) ->
                  let propag_store, propag_vars = propag var_in var_out new_store in   
                  propag_store, List.append propag_vars modified_vars
                ) (store, []) not_fixed
            else
              Store.add (X(-1,-1,-1)) (F,1) store, [X(-1,-1,-1)] in
  time_active_sb := !time_active_sb +. Sys.time () -. t;
  res_store, cstrbdd, res_vars

let propagator_le a b store cstrbdd =
  let bdda,wa = Store.find a store in
  let bddb,wb = Store.find b store in
  let res_a = improved_consistency bdda (upper_bound bddb) wa random_heuristic_improved_consistency in
  let res_b = improved_consistency bddb (lower_bound bdda) wb random_heuristic_improved_consistency in
  Store.add a (res_a,wa) (Store.add b (res_b,wb) store),
  cstrbdd,
  get_modified [a,bdda,res_a;b,bddb,res_b]
  
  
  
(*let time_active_sb = ref 0.
let time_active_sb_not_cons = ref 0.
let time_active_sb_not_cons_int_of_bdd = ref 0.
let test_propagator_active_sb l b store =
  let t = Sys.time () in
  let new_store, modified_vars, rest_bound =
    List.fold_left
      (fun (new_store, modified_vars, rest_bound_acc) (var_in, var_out) ->
        let propag_store, propag_vars = test_propagator_function var_in var_out new_store in   
        let current_out_bdd = fst (Store.find var_out propag_store) in
        (propag_store, List.rev_append propag_vars modified_vars, rest_bound_acc + if is_empty (intersection current_out_bdd input_output_inverse_sbox_proba) then 7 else 6)) (store, [], b) l in
  time_active_sb := !time_active_sb +. Sys.time () -. t;
  if rest_bound > 0 then
    Store.add (X(-1,-1,-1)) (F,1) new_store, [X(-1,-1,-1)]
  else
    new_store, modified_vars*)

let propagate cstr store cstrbdds first =
  let new_store, new_cstrbdd, modified_vars =
    let current_cstrbdd = Cstrmap.find cstr cstrbdds in
    match cstr with
    | Xor(a,b,c) -> propagator_xor a b c store current_cstrbdd
    | Mc(a,b,c,d,e,f,g,h) -> propagator_mc a b c d e f g h store current_cstrbdd first
    | Not_zero(a) -> propagator_not_zero a store current_cstrbdd
    | ActiveSB(l,b) -> propagator_active_sb l !b store current_cstrbdd
    | Iscst(a,i) -> propagator_cst i a store current_cstrbdd
    | Le(a,b) -> propagator_le a b store current_cstrbdd in
  new_store, Cstrmap.add cstr new_cstrbdd cstrbdds, modified_vars
                  
let vars_of_cstr cstr = match cstr with
  (* return a set of strings that are the variables that appear in the given constraint *)
  | Xor(a,b,c) -> Varset.add a (Varset.add b (Varset.add c Varset.empty))
  | Mc(a,b,c,d,e,f,g,h) -> Varset.add a (Varset.add b (Varset.add c (Varset.add d (Varset.add e (Varset.add f (Varset.add g (Varset.add h Varset.empty)))))))
  | Not_zero(a) | Iscst(a,_) -> Varset.add a Varset.empty
  | ActiveSB(l, _) -> List.fold_left (fun acc (var_in, var_out) -> Varset.add var_in (Varset.add var_out acc)) Varset.empty l
  | Le (a,b) -> Varset.add a (Varset.add b Varset.empty)


let time_all_propag = ref 0.
let rec full_propagation cstrset store cstrbdds cstr_of_var =
  let res = 
  match Cstrset.is_empty cstrset with
  | true -> store, cstrbdds
  | false -> let cstr = Cstrset.max_elt cstrset in
             let t = Sys.time () in
             (*print_endline (string_of_cstr cstr);*)
             let new_store, propagated_cstrbdds, modified_vars = propagate cstr store cstrbdds true in
             (*let new_store_weak, modified_vars_weak = propagate cstr store false in*)
             time_all_propag := !time_all_propag +. Sys.time () -. t;
             (*if not (List.exists (fun elt -> is_empty (fst (Store.find elt new_store))) modified_vars) then 
               List.iter (fun elt -> print_endline (string_of_var elt^" "^(B.string_of_big_int (cardinal (cutted_bdd 8 (fst (Store.find elt store)))))^" "^(B.string_of_big_int (cardinal (cutted_bdd 8 (fst (Store.find elt new_store))))))) modified_vars;*)
             if List.exists (fun elt -> if is_empty (fst (Store.find elt new_store)) then true else false) modified_vars then
               Store.empty, cstrbdds
             else
               full_propagation (Cstrset.remove cstr (List.fold_left (fun acc elt -> Cstrset.union acc (Store.find elt cstr_of_var)) cstrset modified_vars)) new_store propagated_cstrbdds cstr_of_var in
  res


                           
let add_or_create var store cstr =
  try Cstrset.add cstr (Store.find var store)
  with Not_found -> Cstrset.singleton cstr

                  
(****************************)
(* Initialization functions *)

(* This function adds the bdd to the store only if it is not already present with a bigger depth *)
let add_list_to_store l store =
  List.fold_left (fun store_acc (key, bdd, width) -> try let current_bdd, _ = Store.find key store_acc in
                                                         if depth current_bdd < depth bdd then Store.add key (bdd,width) store_acc
                                                         else store_acc
                                                     with Not_found -> Store.add key (bdd, width) store_acc) store l
                  
let init_domain cstrset width =
  (* return a couple of (a couple containing the complete store and the map from vars to constraints) and the variables that are in an S-box *)
  Cstrset.fold (fun cstr (store_acc,cstrset_acc,cstrmap_acc) ->
      match cstr with
      | Xor(a,b,c) -> add_list_to_store [a,complete8,width;b,complete8,width;c,complete8,width] store_acc,
                      Store.add a (add_or_create a cstrset_acc cstr) (Store.add b (add_or_create b cstrset_acc cstr) (Store.add c (add_or_create c cstrset_acc cstr) cstrset_acc)),
                      Cstrmap.add cstr (cstr_xor_bdd,width) (* TODO improve computation of this *) cstrmap_acc
      | Mc(a,b,c,d,e,f,g,h) -> add_list_to_store [a,complete8,width;b,complete8,width;c,complete8,width;d,complete8,width;e,complete8,width;f,complete8,width;g,complete8,width;h,complete8,width] store_acc,
                               Store.add a (add_or_create a cstrset_acc cstr) (Store.add b (add_or_create b cstrset_acc cstr) (Store.add c (add_or_create c cstrset_acc cstr) (Store.add d (add_or_create d cstrset_acc cstr) (Store.add e (add_or_create e cstrset_acc cstr) (Store.add f (add_or_create f cstrset_acc cstr) (Store.add g (add_or_create g cstrset_acc cstr) (Store.add h (add_or_create h cstrset_acc cstr) cstrset_acc))))))),
                               Cstrmap.add cstr (F,width) cstrmap_acc
      | Not_zero(a) -> add_list_to_store [a,complete8,width] store_acc, 
                       Store.add a (add_or_create a cstrset_acc cstr) cstrset_acc,
                       Cstrmap.add cstr (F,width) cstrmap_acc
      | Iscst(a,_) -> add_list_to_store [a,complete8,width] store_acc,
                      cstrset_acc,
                      cstrmap_acc
      | ActiveSB(l,_) -> let ws, winverse = Bdd.width input_output_sbox, Bdd.width input_output_inverse_sbox in
                         List.fold_left
                           (fun (complete_acc, cstr_to_var_acc, cstrmap_do_not_touch) (var_in,var_out) ->
                             Store.add var_in (complete8, ws) (Store.add var_out (input_output_inverse_sbox, winverse) complete_acc),
                             Store.add var_in (add_or_create var_in cstr_to_var_acc cstr) (Store.add var_out (add_or_create var_out cstr_to_var_acc cstr) cstr_to_var_acc),
                             cstrmap_do_not_touch) (store_acc, cstrset_acc, Cstrmap.add cstr (F,width) cstrmap_acc) l
      | Le(a,b) -> add_list_to_store [a,complete8,width;b,complete8,width] store_acc,
                      Store.add a (add_or_create a cstrset_acc cstr) (Store.add b (add_or_create b cstrset_acc cstr) cstrset_acc),
                      cstrmap_acc
    ) cstrset (Store.empty, Store.empty, Cstrmap.empty)

(* A function that applies the unary constraints, and return a new store and a new constraint set that are not enforces *)
let propag_of_unary_cstr store cstrset =
  Cstrset.fold (fun cstr (cstr_acc, store_acc) -> match cstr with
                                                  | Iscst(a,i) -> (cstr_acc, let res_store,_,_ = propagator_cst i a store_acc F in res_store)
                                                  | Not_zero(a) -> let new_store, _, modified_vars = propagator_not_zero a store F in
                                                                   begin match modified_vars with
                                                                   | [] -> (Cstrset.add cstr cstr_acc, store)
                                                                   | _ -> (cstr_acc, new_store) end
                                                  | _ -> (Cstrset.add cstr cstr_acc, store_acc)
    ) cstrset (Cstrset.empty, store)
  
(*******************)
(* Split functions *)

let split_proba_sb store sbox_vars =
  List.fold_left
    (fun acc var ->
      match var with
      | X _| K _ | Z _ -> acc
      | SX _ | SK _ -> let bdd,_ = Store.find var store in
                       if not (subset bdd input_output_inverse_sbox_proba || is_empty (intersection bdd input_output_inverse_sbox_proba)) then let _ = Some var in None else acc
    ) None sbox_vars
                                   
let split_store store sbox_vars =
  match split_proba_sb store sbox_vars with
  | None -> let _,chosen_sbox_var = List.fold_left
                                      (fun (card,key) elt -> let bdd_elt, _ = Store.find elt store in if List.mem elt sbox_vars && cardinal bdd_elt > B.unit_big_int then (cardinal bdd_elt,elt) else (card,key)
                                      ) (B.unit_big_int,X(-1,-1,-1)) [X(1,0,1);SX(1,0,1);X(1,0,0);SX(1,0,0)] in
            let _, chosen_sbox_var = if compare_var chosen_sbox_var (X(-1,-1,-1)) = 0 then
                                       (let _ = 1 in List.fold_left
                                                       (fun (card,key) elt -> let bdd_elt, _ = Store.find elt store in if cardinal bdd_elt > B.unit_big_int then (cardinal bdd_elt,elt)
                                                                                                                       else (card,key)
                                                       ) (B.minus_big_int B.unit_big_int,X(-1,-1,-1)) sbox_vars) else B.zero_big_int, chosen_sbox_var in
            let (_,chosen_key) = if compare_var chosen_sbox_var (X(-1,-1,-1)) = 0 then Store.fold (fun k (bdd,_) (card,key) -> if cardinal bdd > card then (cardinal bdd,k) else (card,key)) store (B.unit_big_int,X(-1,-1,-1)) else (B.zero_big_int, chosen_sbox_var) in
            let (chosen_bdd,chosen_width) = Store.find chosen_key store in
            let (bdd1,bdd2) = split_backtrack_first chosen_bdd in
            [ Store.add chosen_key (bdd1,chosen_width) store; Store.add chosen_key (bdd2,chosen_width) store], chosen_key
  | Some var -> let bdd, w = Store.find var store in
                [Store.add var (intersection bdd input_output_inverse_sbox_proba,w) store;Store.add var (diff bdd input_output_inverse_sbox_proba,w) store],var

(******************)
(* Solution Check *)
  
let is_solution_xor a b c cststore =
  let ca = Store.find a cststore in
  let cb = Store.find b cststore in
  let cc = Store.find c cststore in
  ca lxor cb = cc
  
let is_solution_le a b cststore =
  let ca = Store.find a cststore in
  let cb = Store.find b cststore in
  ca <= cb

let is_solution_mc a b c d e f g h cststore =
  let ca = Store.find a cststore in
  let cb = Store.find b cststore in
  let cc = Store.find c cststore in
  let cd = Store.find d cststore in
  let ce = Store.find e cststore in
  let cf = Store.find f cststore in
  let cg = Store.find g cststore in
  let ch = Store.find h cststore in
  let re,rf,rg,rh = mix_column_int ca cb cc cd in
  re = ce && rf = cf && rg = cg && rh = ch

let is_solution_sb a b cststore =
  let csta = Store.find a cststore in
  let cstb = Store.find b cststore in
  if csta = 0 && cstb = 0 then true, 0 else begin
      let outputs = array_diff_sbox_outputs.(csta) in
      Intset.mem (Store.find b cststore) outputs, let r = probaS csta cstb in r
    end

let is_solution_active_sb l b cststore =
  let is_sol, proba =
    List.fold_left (fun (sol_acc, proba_acc) (var_in, var_out) -> let cstr_sol, cstr_proba = is_solution_sb var_in var_out cststore in
                                                                  sol_acc && cstr_sol, proba_acc + cstr_proba) (true, 0) l
  in if proba < b then false,0  else (is_sol, proba)
  
let is_solution_cstr cstr cststore =
  match cstr with
  | Xor(a,b,c) -> is_solution_xor a b c cststore, 0
  | Mc(a,b,c,d,e,f,g,h) -> is_solution_mc a b c d e f g h cststore, 0
  | Not_zero(a) -> Store.find a cststore <> 0, 0
  | ActiveSB(l,b) -> is_solution_active_sb l !b cststore
  | Iscst(a,i) -> Store.find a cststore = i, 0
  | Le(a,b) -> is_solution_le a b cststore, 0

let time_is_solution = ref 0.
let is_solution cstrset cststore =
  let t = Sys.time () in
  let res = Cstrset.fold (fun cstr (b_acc, prob_acc) -> if b_acc then (let b, prob = is_solution_cstr cstr cststore in b, prob + prob_acc) else b_acc, 0) cstrset (true, 0) in
  time_is_solution := !time_is_solution +. Sys.time () -. t;
  res
  
let store_size store =
  Store.fold (fun _ (v,_) acc -> B.mult_big_int (cardinal v) acc) store B.unit_big_int
  
let time_full_propag = ref 0.
let nb_nodes = ref 0
let nb_fails = ref 0
let rec backtrack cstrset store cstrbdds acc depth modified_var (cstr_of_var, sbox_vars, cstr_bound, one_cst) =
  let t = Sys.time () in
  incr nb_nodes;
  let propagated_store, propagated_cstrbdds = full_propagation 
                           (match modified_var with
                            | None -> cstrset
                            | Some _ when depth mod 2 = 3 -> Cstrset.empty
                            | Some a -> Store.find a cstr_of_var)
                           store cstrbdds cstr_of_var in
  time_full_propag := !time_full_propag +. Sys.time () -. t;
  (*Store.iter (fun k (bdd,_) -> if cardinal bdd > B.unit_big_int then print_endline ((string_of_var k)^" "^(B.string_of_big_int (cardinal bdd)))) propagated_store;*)
  match Store.is_empty propagated_store, store_size propagated_store with
  | true, _ -> incr nb_fails;acc
  | _, n when n = B.zero_big_int -> incr nb_fails;acc
  | _, n when n = B.unit_big_int -> let cststore = Store.fold (fun key (bdd,_) acc -> Store.add key (int_of_bdd (cutted_bdd 8 bdd)) acc) propagated_store Store.empty in
                                    let is_sol, prob = is_solution cstrset cststore in
                                    if is_sol then (print_endline "one_solution"; print_endline ("proba = "^(string_of_int prob));cstr_bound := prob + 1;(cststore, prob)) else (incr nb_fails;acc)
  | _ -> let split_stores, split_var = split_store propagated_store sbox_vars in
         List.fold_left (fun new_acc backtrack_store -> backtrack cstrset backtrack_store propagated_cstrbdds new_acc (depth+1) (Some split_var) (cstr_of_var, sbox_vars, cstr_bound, one_cst)) acc split_stores
     















          

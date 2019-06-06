let generate_program r key_size =
  (* Generates the crypto program, currently for aes 128 *)
  if key_size != 128 then failwith "bad key size";
  let underscores a b c = string_of_int a^"_"^(string_of_int b)^"_"^(string_of_int c) in
  let s = ref "" in
  for j=0 to 3 do
    for k=0 to 3 do
      s := !s^"XOR(xinit_"^(string_of_int j)^"_"^(string_of_int k)^", k_"^(underscores 0 j k)^", x_"^(underscores 0 j k)^");\n"
    done
  done;
  for i= 0 to r-1 do
    if i <> 0 then (* On first round the bytes of X are computed from the input *)
      for j=0 to 3 do
        for k=0 to 3 do
          s := !s^"XOR(z_"^(underscores (i-1) j k)^", k_"^(underscores i j k)^", x_"^(underscores i j k)^");\n"
        done
      done;
    for j=0 to 3 do
      for k=0 to 3 do
        s := !s^"SB(x_"^(underscores i j k)^", sx_"^(underscores i j k)^");\n"
      done
    done;
    if i <> r-1 then (* No MC on last round *)
      for k=0 to 3 do
        s := !s^"MC(sx_"^(underscores i 0 k)^", sx_"^(underscores i 1 ((k+1) mod 4))^", sx_"^(underscores i 2 ((k+2) mod 4))^", sx_"^(underscores i 3 ((k+3) mod 4))^", z_"^(underscores i 0 k)^", z_"^(underscores i 1 k)^", z_"^(underscores i 2 k)^", z_"^(underscores i 3 k)^");\n" (* In this step, we use the values shifted on the right, so to get them we need to look on the left *)
      done;
    if i <> r then begin
        for j=0 to 3 do
          s := !s^"SB(k_"^(underscores i j 3)^", sk_"^(underscores i j 3)^");\n";
        done;
        if i <> r-1 then begin
        for j=0 to 3 do
          s := !s^"XOR(k_"^(underscores (i+1) j 0)^",k_"^(underscores i j 0)^", sk_"^(underscores i ((j+1) mod 4) 3)^");\n"
        done;
        for j=0 to 3 do
          for k=1 to 3 do
            s := !s^"XOR(k_"^(underscores (i+1) j k)^", k_"^(underscores (i+1) j (k-1))^", k_"^(underscores i j k)^");\n"
          done
        done end
      end;
  done;
  !s^"&"

let _ = print_string (generate_program (int_of_string Sys.argv.(1)) (int_of_string Sys.argv.(2)))

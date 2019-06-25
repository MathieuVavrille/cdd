%{
    open Solver
    let all_sbox = ref []
    let sbox_inactive = ref Varset.empty
%}

/* description des lexèmes, ceux-ci sont décrits dans lexer.mll */

%token <int> INT
%token XOR MC SB CST LE
%token COMMA SEMIC
%token LPAREN RPAREN UNDER
%token ZERO NOTZERO
%token XUNDER XINIT SXUNDER KUNDER SKUNDER ZUNDER
%token END


%start main
%type <Solver.Cstrset.t * Solver.var list * int ref> main
%%

main:
  | cstr           { let cstrset = $1 in
		     let active_sbox_list = List.fold_left (fun acc (x,y) -> if Varset.mem x !sbox_inactive then acc else (x,y)::acc)
							   [] !all_sbox in
		     let cstr_bound = ref (-7 * List.length active_sbox_list) in
		     List.fold_left (fun acc (x,y) -> if Varset.mem x !sbox_inactive then Cstrset.add (Iscst(y,0)) acc else acc) (Cstrset.add (ActiveSB(active_sbox_list, cstr_bound)) cstrset) !all_sbox, List.fold_left (fun acc (a,b) -> if Varset.mem a !sbox_inactive then acc else a::b::acc) [] !all_sbox, cstr_bound }

cstr:
  | END            { Cstrset.empty }
  | LE LPAREN variable COMMA variable RPAREN SEMIC cstr                 { Cstrset.add (Le($3,$5)) $8 }
  | XOR LPAREN variable COMMA variable COMMA variable RPAREN SEMIC cstr { Cstrset.add (Xor($3, $5, $7)) $10 }
  | MC LPAREN variable COMMA variable COMMA variable COMMA variable COMMA variable COMMA variable COMMA variable COMMA variable RPAREN SEMIC cstr { Cstrset.add (Mc($3, $5, $7, $9, $11, $13, $15, $17)) $20 }
  | SB LPAREN variable COMMA variable RPAREN SEMIC cstr { all_sbox := ($3, $5)::(!all_sbox); $8 }
  | ZERO LPAREN variable RPAREN SEMIC cstr { sbox_inactive := Varset.add $3 !sbox_inactive;Cstrset.add (Iscst($3,0)) $6 }
  | NOTZERO LPAREN variable RPAREN SEMIC cstr { Cstrset.add (Not_zero($3)) $6 }
  | CST LPAREN variable COMMA INT RPAREN SEMIC cstr  { Cstrset.add (Iscst($3, $5)) $8 }


variable:
  | XUNDER INT UNDER INT UNDER INT     { X($2,$4,$6) }
  | XINIT INT UNDER INT                { X(-1,$2,$4) }
  | SXUNDER INT UNDER INT UNDER INT    { SX($2,$4,$6) }
  | KUNDER INT UNDER INT UNDER INT     { K($2,$4,$6) }
  | SKUNDER INT UNDER INT UNDER INT    { if $6 = 3 then SK($2,$4) else failwith "The sbox key is not on third column" }
  | ZUNDER INT UNDER INT UNDER INT     { Z($2,$4,$6) }
;

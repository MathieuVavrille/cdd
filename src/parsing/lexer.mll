{
open Parser;;        (* le type "token" est défini dans parser.mli *)

exception Eof;;
}

rule token = parse    (* la "fonction" aussi s'appelle token *)

  | '&'      	      	      { END }    
  | ';' 		      { SEMIC }
  | ',' 		      { COMMA }
  | '('                       { LPAREN }
  | ')'                       { RPAREN }
  | '_' 		      { UNDER }

  | "ZERO"		      { ZERO }
  | "NOT_ZERO"		      { NOTZERO }
  | "XOR"		      { XOR }
  | "SB" 		      { SB }
  | "MC" 		      { MC }
  | "CST" 		      { CST }
  | "x_" 		      { XUNDER }
  | "xinit_"		      { XINIT }
  | "sx_" 		      { SXUNDER }
  | "k_" 		      { KUNDER }
  | "sk_" 		      { SKUNDER }
  | "z_" 		      { ZUNDER }
  | '_' 		      { UNDER }

  | (['0'-'9']* as s) 	   	       		       { INT (int_of_string s) }
  | [' ' '\t' '\n']           			       { token lexbuf }  
  | "(*" ('*'[^')'] | [^'*'])* '*'? "*)"       	       { token lexbuf }  (* Comments *)




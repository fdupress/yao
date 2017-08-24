
(* The type of tokens. *)

type token = 
  | SCOLON
  | RANGLE
  | OTR2
  | OTR1
  | LANGLE
  | INT of (string)
  | I2
  | I1
  | GR
  | FN
  | EQ
  | EOF

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Utils.input * Utils.input * ((int * int * int * int array * int array) * (bool * bool * bool * bool) array) * Utils.randomness list)

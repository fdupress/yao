# 1 "src/sfeLexer.mll"
 
  open SfeParser

# 6 "src/sfeLexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\241\255\242\255\023\000\000\000\000\000\078\000\014\000\
    \250\255\251\255\252\255\253\255\254\255\255\255\248\255\249\255\
    \247\255\001\000\032\000\245\255\246\255\244\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\012\000\013\000\013\000\012\000\013\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_default = 
   "\002\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\255\255\000\000\000\000\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\012\000\013\000\000\000\000\000\012\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \012\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\000\000\011\000\009\000\010\000\008\000\015\000\
    \014\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\020\000\019\000\000\000\000\000\000\000\000\000\000\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\000\000\000\000\
    \000\000\003\000\003\000\003\000\003\000\003\000\006\000\004\000\
    \000\000\007\000\000\000\000\000\000\000\000\000\000\000\005\000\
    \000\000\000\000\021\000\018\000\017\000\000\000\000\000\000\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\255\255\255\255\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\000\000\007\000\
    \007\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\018\000\018\000\255\255\255\255\255\255\255\255\255\255\
    \003\000\003\000\003\000\003\000\003\000\003\000\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\255\255\255\255\255\255\255\255\255\255\000\000\
    \255\255\255\255\004\000\017\000\005\000\255\255\255\255\255\255\
    \003\000\003\000\003\000\003\000\003\000\003\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\006\000\
    \006\000\006\000\006\000\006\000\006\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\006\000\
    \006\000\006\000\006\000\006\000\006\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\006\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec main lexbuf =
    __ocaml_lex_main_rec lexbuf 0
and __ocaml_lex_main_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 10 "src/sfeLexer.mll"
                      ( Lexing.new_line lexbuf; main lexbuf )
# 127 "src/sfeLexer.ml"

  | 1 ->
# 11 "src/sfeLexer.mll"
                      ( main lexbuf )
# 132 "src/sfeLexer.ml"

  | 2 ->
# 12 "src/sfeLexer.mll"
                      ( SCOLON )
# 137 "src/sfeLexer.ml"

  | 3 ->
# 13 "src/sfeLexer.mll"
                      ( EQ )
# 142 "src/sfeLexer.ml"

  | 4 ->
# 14 "src/sfeLexer.mll"
                      ( LANGLE )
# 147 "src/sfeLexer.ml"

  | 5 ->
# 15 "src/sfeLexer.mll"
                      ( RANGLE )
# 152 "src/sfeLexer.ml"

  | 6 ->
# 17 "src/sfeLexer.mll"
                      ( I1 )
# 157 "src/sfeLexer.ml"

  | 7 ->
# 18 "src/sfeLexer.mll"
                      ( I2 )
# 162 "src/sfeLexer.ml"

  | 8 ->
# 19 "src/sfeLexer.mll"
                      ( FN )
# 167 "src/sfeLexer.ml"

  | 9 ->
# 20 "src/sfeLexer.mll"
                      ( OTR1 )
# 172 "src/sfeLexer.ml"

  | 10 ->
# 21 "src/sfeLexer.mll"
                      ( OTR2 )
# 177 "src/sfeLexer.ml"

  | 11 ->
# 22 "src/sfeLexer.mll"
                      ( GR )
# 182 "src/sfeLexer.ml"

  | 12 ->
# 24 "src/sfeLexer.mll"
                      ( INT (Lexing.lexeme lexbuf) )
# 187 "src/sfeLexer.ml"

  | 13 ->
let
# 25 "src/sfeLexer.mll"
         c
# 193 "src/sfeLexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 25 "src/sfeLexer.mll"
                      ( Printf.printf "unknown token %c\n%!" c; 
                        failwith "Unknwon token" )
# 198 "src/sfeLexer.ml"

  | 14 ->
# 27 "src/sfeLexer.mll"
                      ( EOF )
# 203 "src/sfeLexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_main_rec lexbuf __ocaml_lex_state

;;


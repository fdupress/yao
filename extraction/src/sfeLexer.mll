{
  open SfeParser
}

let blank    = [' ' '\t' '\r']
let newline  = '\n'
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']

rule main = parse
  | newline           { Lexing.new_line lexbuf; main lexbuf }
  | blank             { main lexbuf }
  | ";"               { SCOLON }
  | "="               { EQ }
  | "<"               { LANGLE }
  | ">"               { RANGLE }

  | "i1"              { I1 }
  | "i2"              { I2 }
  | "fn"              { FN }
  | "otr1"            { OTR1 }
  | "otr2"            { OTR2 }
  | "gr"              { GR }

  | hexdigit+         { INT (Lexing.lexeme lexbuf) }
  | _ as c            { Printf.printf "unknown token %c\n%!" c; 
                        failwith "Unknwon token" }
  | eof               { EOF }

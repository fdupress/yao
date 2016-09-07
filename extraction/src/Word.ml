type top_Concrete_W_word = string

let _dtlb_rb :  top_Concrete_W_word -> int -> bool = fun t n ->
  let c = Char.code (t.[n/8]) in
  let c = c land (1 lsl (n mod 8)) in
  c > 0
  
let _dtlb_lsmn_rb :  top_Concrete_W_word -> int -> bool ->  top_Concrete_W_word = fun t n v ->
  let t = t in
  let q = n / 8 in
  let r = n mod 8 in
  let c = Char.code t.[q] in
  let mask = 0x01 lsl r in
  let c = if v then c lor mask else c land (0xFF lxor mask) in
  t.[q] <- Char.chr c;
  t
                             
let top_Concrete_W_zeros : top_Concrete_W_word = String.make 16 '\000'

let top_Concrete_W_from_int : int -> top_Concrete_W_word = fun inttok ->
  let tok = top_Concrete_W_zeros in
  let inttokr = ref inttok in
  for i = 0 to 7 do
      tok.[i] <- Char.chr (!inttokr mod 256);
      inttokr := !inttokr / 256;
  done;
  tok
                                                             
let top_Concrete_W_getlsb (w:top_Concrete_W_word) =
  _dtlb_rb w 0

let top_Concrete_W_setlsb (w:top_Concrete_W_word) (b:bool) = 
  _dtlb_lsmn_rb w 0 b
  
let top_Concrete_W_cf (a:top_Concrete_W_word) (b:top_Concrete_W_word) =
  let r = top_Concrete_W_zeros in
  for i = 0 to 15 do
    r.[i] <- Char.chr ((Char.code a.[i]) lxor (Char.code b.[i]))
  done;
  r

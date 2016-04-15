type word = string
    
let _dtlb_rb : word -> int -> bool = fun t n ->
  let c = Char.code (t.[n/8]) in
  let c = c land (1 lsl (n mod 8)) in
  c > 0
  

let _dtlb_lsmn_rb : word -> int -> bool -> word = fun t n v ->
  	let t = String.copy t in
    let q = n / 8 in
    let r = n mod 8 in
    let c = Char.code t.[q] in
    let mask = 0x01 lsl r in
    let c = if v then c lor mask else c land (0xFF lxor mask) in
    t.[q] <- Char.chr c;
    t

let zeros : word =
  String.make 16 '\000'

let from_int : int -> word = fun inttok ->
  let tok = String.copy zeros in
  let inttokr = ref inttok in
  for i = 0 to 7 do
      tok.[i] <- Char.chr (!inttokr mod 256);
      inttokr := !inttokr / 256;
  done;
  tok

let getlsb (b : word) =
  _dtlb_rb b 0

let setlsb (b : word) (v : bool) =
  _dtlb_lsmn_rb b 0 v

let cf (a:word) (b:word) =
	let r = String.copy zeros in
  for i = 0 to 15 do
    r.[i] <- Char.chr ((Char.code a.[i]) lxor (Char.code b.[i]))
  done;
  r
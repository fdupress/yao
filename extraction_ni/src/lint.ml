(*#if defined(USEMPZ)
open Mpz

type t = Mpz.t

let of_string = Mpz.of_string
let to_string = Mpz.to_string

let zero:t = of_string "0" 

let add_mod (a:t) b m = 
  let res = Mpz.init() in
  Mpz.add res a b;
  if Mpz.cmp res m < 0 then res else (Mpz.sub res res m; res)

let opp_mod (a:t) m = 
  if Mpz.cmp a zero = 0 then a
  else 
    let res = Mpz.init() in
    Mpz.sub res m a; res

let sub_mod (a:Mpz.t) b m = 
  let res = Mpz.init() in
  Mpz.sub res a b;
  if Mpz.cmp res zero < 0 then (Mpz.add res res m; res) else res

let powm (a:Mpz.t) e m =
  let res = Mpz.init() in
  Mpz.powm res a e m;
  res

let div_mod (a:Mpz.t) b m = 
  let res = Mpz.init () in
  let b = Mpz.invert res b m in
  assert b;
  Mpz.mul res res a;
  Mpz.gmod res res m;
  res
  
let state =
  Gmp_random.init_default ()

let random (n:Mpz.t) =
  let res = Mpz.init () in
  Gmp_random.Mpz.urandomm res state n;
  res

#else*)
open Gmp

type t = Z.t

let of_string = Z.from_string_base ~base:10
let to_string = Z.to_string_base ~base:10
             
let zero = Z.zero

let add_mod a b m = 
  let r = Z.add a b in
  if Z.Infixes.(<!) r m then r else Z.sub r m

let opp_mod a m = 
  if Z.Infixes.(=!) a Z.zero then a
  else Z.sub m a

let sub_mod a b m = 
  let r = Z.sub a b in
  if Z.Infixes.(<!) r Z.zero then Z.add r m else r

let powm a e m = 
  Z.powm a e m

let div_mod a b m =
  match Z.inverse b m with
  | None -> assert false
  | Some b -> Z.dmod (Z.mul a b) m

let random n = 
  Z.urandomm ~state:RNG.default ~n 
             (*#endif*)

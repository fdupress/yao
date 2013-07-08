require import Bitstring.
require import Dkc.
require import Map.
require import Array.
require import Int.
require import Pair.
require import Bool.


type token = bitstring.
type tokens = (token*token) array.
type 'a gate = 'a*'a*'a*'a.
type fGate = bool gate.
type gGate = token gate.

op lsb(b:token) : bool = b.[0].

op getTok(x:tokens, a:int, i:bool) : token =
  if i then snd x.[a] else fst x.[a].

op setTok(x:tokens, a:int, i:bool, t:token) : tokens =
  if i then x.[a <- (fst x.[a], t)] else x.[a <- (t, snd x.[a])].

lemma set_get_tok: forall (x:tokens, a:int, i:bool, t:token, b:int, j:bool),
  0 <= b => b < length x =>
  getTok (setTok x a i t) b j = (a=b/\i=j)?t:getTok x b j.
intros=> ? ? ? ? ? ? ? ?.
simplify setTok getTok.
by case i=> ?;case j=> ?;rewrite ! set_get //;case (a=b)=> ?;subst;trivial.
save.

lemma set_set_tok: forall (x:tokens, a:int, i:bool, t:token, u:token),
  0 <= a => a < Array.length x =>
  setTok (setTok x a i t) a i u = (setTok x a i u).
  intros=> ? ? ? ? ? ? ?.
  simplify setTok fst snd.
  case i=> ?;simplify;rewrite set_setE  set_get //. 
save.

op intToBitstring = zeros.

lemma intToBitstring_inj : forall g gg,
0 <= g => 0 <= gg =>
intToBitstring g = intToBitstring gg =>
g = gg.
intros=> ? ? ? ?.
rewrite /intToBitstring -Bits.rw_ext /Bits.(==)! zeros_length //.
save.

op tweak(g:int, a:bool, b:bool) : bitstring = a::(b::(intToBitstring g)).

lemma tweak_inj :
  forall g a b gg aa bb, 0 <= g => 0 <= gg =>
     tweak g a b = tweak gg aa bb => (g, a, b) = (gg, aa, bb).
intros ? ? ? ? ? ? ? ?.
simplify tweak.
rewrite ! Bits.cons_inj=> [[? ?] ?].
subst;split=> //.
apply intToBitstring_inj=> //.
save.


op evalGate(f:'a gate, i:bool*bool) : 'a =
  let (ff, ft, tf, tt) = f in
  let (i1, i2) = i in
  if !i1 && !i2 then ff else
  if !i1 && i2 then ft else
  if  i1 && !i2 then tf else
  tt.

op setGateVal(f:'a gate, i:bool*bool, v:'a) : 'a gate =
  let (ff, ft, tf, tt) = f in
  let (i1, i2) = i in
  if !i1 && !i2 then ( v, ft, tf, tt) else
  if !i1 &&  i2 then (ff,  v, tf, tt) else
  if  i1 && !i2 then (ff, ft,  v, tt) else
  (ff, ft, tf,  v).

pred tokenCorrect(n:int, q:int, m:int, x:tokens) =
  Array.length x = (n+q) /\
  (forall (i:int), 0 <= i => i < n + q =>
    (lsb (getTok x i false)) <> (lsb (getTok x i true))) /\
  (forall (i:int), n + q - m <= i => i < n + q =>
    !(lsb (getTok x i false)) ).

op enc(x:tokens, f:fGate, a:int, b:int, g:int, x1:bool, x2:bool) : token =
  let xx1 = (lsb (getTok x a true) = x1) in
  let xx2 = (lsb (getTok x b true) = x2) in
  DKC.encode
    (tweak g x1 x2)
    (getTok x a xx1)
    (getTok x b xx2)
    (getTok x g (evalGate f (xx1,xx2))).


op garbleGate(x:tokens, f:fGate, a:int, b:int, g:int) : gGate =
  (
    enc x f a b g false false,
    enc x f a b g false  true,
    enc x f a b g  true false,
    enc x f a b g  true  true
  ).

lemma inverse_base :
    forall (i: bool*bool) ,
    forall (n q m a b g : int) ,
    forall (f : fGate) ,
    forall (x : tokens) ,
      (n > 0) =>
      (q > 0) =>
      (m > 0) =>
      (0 <= a) /\ (a < g) =>
      (0 <= b) /\ (b < g) =>
      (n <= g /\ g < n + q) =>
      tokenCorrect n q m x =>
      let gi1 = getTok x a (fst i) in
      let gi2 = getTok x b (snd i) in
      DKC.decode
        (tweak g (lsb gi1) (lsb gi2)) gi1 gi2 
        (evalGate
          (garbleGate x f a b g)
          (lsb gi1, lsb gi2)
        ) = getTok x g (evalGate f i).
proof.
  do intros ?.
  rewrite -(DKC.inverse (tweak g (lsb gi1) (lsb gi2)) gi1 gi2 (getTok x g (evalGate f i))).
  congr=> //. 
  simplify evalGate garbleGate enc.
  generalize H5.
  case (! lsb gi1 && ! lsb gi2)=> h;smt.
save.

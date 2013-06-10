require import Bitstring.
require import Dkc.
require import Map.
require import Array.
require import Int.
require import Pair.
require import Bool.
require Array.


type token = Dkc.number.
type tokens = (token*token) array.
type 'a gate = 'a*'a*'a*'a.
type fGate = bool gate.
type gGate = token gate.

op lsb(b:bitstring) : bool = b.[0].

op getTok(x:tokens, a:int, i:bool) : token =
  if i then snd x.[a] else fst x.[a].

op setTok(x:tokens, a:int, i:bool, t:token) : tokens =
  if i then x.[a <- (fst x.[a], t)] else x.[a <- (t, snd x.[a])].

op intToBitstring : int -> bitstring.

op tweak(g:int, a:bool, b:bool) : bitstring = a::(b::(intToBitstring g)).

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
  Dkc.encode
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
      Dkc.decode
        (tweak g (lsb gi1) (lsb gi2)) gi1 gi2 
        (evalGate
          (garbleGate x f a b g)
          (lsb gi1, lsb gi2)
        ) = getTok x g (evalGate f i).
proof.
  intros i n q m a b g f x.
  intros npos qpos mpos avalid bvalid gvalid tokCor.
  intros gi1 gi2.
  cut main : (forall (inter:bool),
    (evalGate f (fst i, snd i) = inter) =>
      Dkc.decode
        (tweak g (lsb gi1) (lsb gi2))
        gi1
        gi2
        (evalGate (garbleGate x f a b g) (lsb gi1,lsb gi2))
      = getTok x g inter
  );[|trivial].
  intros inter h1.
  delta evalGate garbleGate.
  simplify.
  cut removeIf : ((
    if !lsb gi1 && !lsb gi2 then enc x f a b g false false else
    if !lsb gi1 &&  lsb gi2 then enc x f a b g false  true else
    if  lsb gi1 && !lsb gi2 then enc x f a b g  true false else
    enc x f a b g true true) = enc x f a b g (lsb gi1) (lsb gi2));[trivial|].
  rewrite removeIf.
  delta enc gi1 gi2.
  simplify.
  rewrite (_:(lsb (getTok x a true) = lsb (getTok x a (fst i))) = (fst i));[trivial|].
  rewrite (_:(lsb (getTok x b true) = lsb (getTok x b (snd i))) = (snd i));[trivial|].
  rewrite h1.
  trivial.
save.
require import Bitstring.
require import Dkc.
require import Map.
require import Array.
require import Int.
require import Pair.
require import Bool.

require import MyTools.

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
rewrite ! Bits.cons_inj=> [? [? ?]].
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
    (forall (t k1 k2 m:Dkc.t), DKC.decode t k1 k2 (DKC.encode t k1 k2 m) = m) =>
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
  intros DKCinv.
  do intros ?.
  rewrite -(DKCinv (tweak g (lsb gi1) (lsb gi2)) gi1 gi2 (getTok x g (evalGate f i))).
  congr=> //. 
  simplify evalGate garbleGate enc.
  generalize H5.
  case (! lsb gi1 && ! lsb gi2)=> h;smt.
save.


type w2g = int array.
type 'a g2v = ('a*'a*'a*'a) array.
type 'a functGen = int*int*int*w2g*w2g*('a g2v).

(*Access to funct member*)
op getN(f:'a functGen) : int =
  let (n, m, q, a, b, g) = f in n.
op getM(f:'a functGen) : int =
  let (n, m, q, a, b, g) = f in m.
op getQ(f:'a functGen) : int =
  let (n, m, q, a, b, g) = f in q.
op getA(f:'a functGen) : w2g =
  let (n, m, q, a, b, g) = f in a.
op getB(f:'a' functGen) : w2g =
  let (n, m, q, a, b, g) = f in b.
op getG(f:'a functGen) : 'a g2v =
  let (n, m, q, a, b, g) = f in g.

op evalComplete(f:'a functGen, x:'a array, extract:'a functGen -> int -> 'a array -> 'a) : 'a array =
  appendInit x ((getN f)+(getQ f)) (extract f).

op evalGen(f:'a functGen, x:'a array, extract:'a functGen -> int -> 'a array -> 'a) : 'a array =
  Array.sub (evalComplete f x extract) ((getN f) + (getQ f) - (getM f)) (getM f).

op extract(f:bool functGen, g:int, x:bool array) : bool =
  evalGate (getG f).[g] (x.[(getA f).[g]], x.[(getB f).[g]]).

  
op extractG(ff:token functGen, g:int, x:token array) =
  let a = (getA ff).[g] in
  let b = (getB ff).[g] in
  let aA = x.[a] in
  let bB = x.[b] in
  let a = lsb aA in
  let b = lsb bB in
  let t = tweak g a b in
  DKC.decode t aA bB (evalGate ((getG ff).[g]) (a, b)).


op garbMap(x:tokens, f:bool functGen, g:int) : token*token*token*token =
  garbleGate x (getG f).[g] (getA f).[g] (getB f).[g] g.

op choose(k:(token*token) array, i:bool array, j:int) : token = getTok k j i.[j].

op validCircuit(bound:int, f:(bool functGen)) =
  let (n, m, q, aa, bb, gg) = f in
  n > 1 /\ m > 0 /\ q > 0 /\ q >= m /\
  n + q - m = bound /\
  length aa = n + q /\ length bb = n + q /\ length gg = n + q /\
  (range n (n+q) true (lambda i b, b /\ aa.[i] >= 0 /\ bb.[i] < i /\ bb.[i] < n+q-m /\ aa.[i] < bb.[i])).

lemma valid_wireinput :
  forall (bound:int) (f:(bool functGen)),
    validCircuit bound f <=> 
  let (n, m, q, aa, bb, gg) = f in
  n > 1 /\ m > 0 /\ q > 0 /\ q >= m /\
  n + q - m = bound /\
  Array.length aa = n + q /\ Array.length bb = n + q /\ Array.length gg = n + q /\
      (forall i,
         i >= n  => i < n+q =>
           aa.[i] >= 0 /\
           bb.[i] < i /\
           bb.[i] < n+q-m /\
           aa.[i] < bb.[i]).
delta validCircuit.
intros bound f.
elim/tuple6_ind f.
intros n m q aa bb gg valF.
case (n > 1);last simplify;smt.
case (m > 0);last simplify;split.
case (q > 0);last simplify;split.
case (n + q - m = bound);last simplify;split.
case (length aa = n + q);last simplify;split.
case (length bb = n + q);last simplify;split.
case (length gg = n + q);last simplify;split.
intros H1 H2 H3 H4 H5 H6 H7.
rewrite (_:(n > 1) = true);first smt.
simplify.
apply (_:forall a b d, (b <=> d) => (a /\ b <=> a /\ d));first smt.
pose {1 3} j := q.
elim/Induction.induction j;last first;first 2 smt.
simplify => k hypJ hypRec.
rewrite range_ind;first smt.
rewrite (_:(n + (k+1) - 1 = n + k));first smt.
rewrite hypRec.
simplify.
split => h.
elim h => h1 h2 i.
case (i = n + k).
  intros => -> _ _.
apply h2.
intros hh1 hh2 hh3.
apply h1.
assumption.
smt.
(split;first intros i hI hI2);apply h;smt.
save.

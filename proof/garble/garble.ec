require import Int.
require import Array.
require import Pair.
require import Bool.

require import Hypothesis.
require import Scheme.
require import GarbleTools.
require import MyTools.

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

op validCircuit(f:(bool functGen)) =
  let (n, m, q, aa, bb, gg) = f in
  n > 1 /\ m > 0 /\ q > 0 /\ q >= m /\
  length aa = n + q /\ length bb = n + q /\ length gg = n + q /\
  (range n (n+q) true (lambda i b, b /\ aa.[i] >= 0 /\ bb.[i] < i /\ bb.[i] < n+q-m /\ aa.[i] < bb.[i])).

lemma valid_wireinput :
  forall (f:(bool functGen)),
    validCircuit f <=> 
  let (n, m, q, aa, bb, gg) = f in
  n > 1 /\ m > 0 /\ q > 0 /\ q >= m /\
  length aa = n + q /\ length bb = n + q /\ length gg = n + q /\
      (forall i,
         i >= n  => i < n+q =>
           aa.[i] >= 0 /\
           bb.[i] < i /\
           bb.[i] < n+q-m /\
           aa.[i] < bb.[i]).
delta validCircuit.
intros f.
elimT tuple6_ind f.
intros x1 x2 x3 x4 x5 x6 valF.
case (x1 > 1);last simplify;smt.
case (x2 > 0);last simplify;split.
case (x3 > 0);last simplify;split.
case (length x4 = x1 + x3);last simplify;split.
case (length x5 = x1 + x3);last simplify;split.
case (length x6 = x1 + x3);last simplify;split.
intros H1 H2 H3 H4 H5 H6.
rewrite (_:(x1 > 1) = true);first smt.
simplify.
apply (_:forall a b d, (b <=> d) => (a /\ b <=> a /\ d));first smt.
apply (Induction.induction
(lambda j,
  range x1 (x1 + j) true
  (lambda (i : int) (b : bool),
     b /\
     x4.[i] >= 0 /\ x5.[i] < i /\ x5.[i] < x1 + x3 - x2 /\ x4.[i] < x5.[i]) <=>
forall (i : int),
  i >= x1 =>
  i < x1 + j =>
  x4.[i] >= 0 /\ x5.[i] < i /\ x5.[i] < x1 + x3 - x2 /\ x4.[i] < x5.[i]) _ _ x3 _
);last first;first 2 smt.
simplify => j hypJ hypRec.
rewrite range_ind;first smt.
rewrite (_:(x1 + j - 1 = x1 + (j - 1)));first smt.
rewrite hypRec.
simplify.
split => h.
elim h => h1 h2 i.
case (i = x1 + (j - 1)).
  intros => -> _ _.
apply h2.
intros hh1 hh2 hh3.
apply h1.
assumption.
smt.
(split;first intros i hI hI2);apply h;smt.
save.

clone Scheme as Garble with

  (*Types*)
  type funct = bool functGen,
  type functG = token functGen,
  type input = bool array,
  type output = bool array,
  type keyInput = (token*token) array,
  type keyOutput = unit,
  type inputG = token array,
  type outputG = token array,
  type tPhi = int*int*int*w2g*w2g,
  
  type random = tokens,


  (*Correction predicat*)
  pred functCorrect(f:funct) =
    (getN f) > 0 /\
    (getM f) > 0 /\
    (getM f) <= (getQ f) /\
    (forall (i:int),
      (getN f) <= i /\ i < (getQ f)+(getN f) =>
        0 <= (getA f).[i] /\ (getA f).[i] < i /\
        0 <= (getB f).[i] /\ (getB f).[i] < i),
  pred randomCorrect(f:funct, x:tokens) =
    tokenCorrect (getN f) (getQ f) (getM f) x,
  pred inputCorrect(f:funct, i:input) =
    (getN f) = Array.length i,

  op k = DKC.k,

  (*Operator*)
  op phi(f:funct) =
    let (n, m, q, aa, bb, gg) = f in
    (n, m, q, aa, bb),

  op phiG(f:functG) =
    let (n, m, q, aa, bb, gg) = f in
    (n, m, q, aa, bb),

  op eval(f:funct, i:input) = evalGen f i extract,

  op evalG(f:functG, i:inputG) = evalGen f i extractG,

  op garble(x:tokens, f:funct) =
    let pp = init ((getN f)+(getQ f)) (garbMap x f) in
    let ff = ((getN f), (getM f), (getQ f), (getA f), (getB f), pp) in
    (ff, Array.sub x 0 (getN f), tt),

  op encrypt(k:keyInput, i:input) = init (Array.length i) (choose k i),
  
  op decrypt(k:keyOutput, o:outputG) = map lsb o,

  op queryValid(query:query) =
    let query0 = fst query in
    let query1 = snd query in
    validCircuit (fst query0) /\ validCircuit (fst query1) /\
    length (snd query0) = getN (fst query0) /\ length (snd query1) = getN (fst query1) /\
    Garble.eval (fst query0) (snd query0) = Garble.eval (fst query1) (snd query1) /\
    phi (fst query0) = phi (fst query1) /\
    (getN (fst query0)) + (getQ (fst query0)) - (getM (fst query0)) = bound /\
    (getN (fst query1)) + (getQ (fst query1)) - (getM (fst query1)) = bound.

export Garble.

module RandGarble : Rand_t = {
  fun gen(f:funct, x:input) : random = {
    var i:int;
    var t:bool array;
    var xx : tokens;
    var tok : token;

    i = 0;
    while (i < (getN f)+(getQ f)-(getM f)-1) {
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < (getN f)+(getQ f)-1) {
      t.[i] = false;
      i = i + 1;
    }

    i = 0;
    while (i < (getN f)+(getQ f)-1) {
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok  (! t.[i]);
      xx = setTok xx i true tok;
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok t.[i];
      xx = setTok xx i false tok;
      i = i + 1;
    }
    return xx;
  }
}.


op eval2(f:funct, i:input, k:int) = (evalComplete f i extract).[k].
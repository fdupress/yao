require import Int.
require import Array.
require import Pair.
require import Bool.

require import Dkc.
require import Scheme.
require import GarbleTools.
require import MyTools.

type w2g = int array.
type 'a g2v = ('a*'a*'a*'a) array.
type 'a functGen = int*int*int*w2g*w2g*('a g2v).

op borne : int.
axiom borneInf : borne > 1.

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
  Dkc.decode t aA bB (evalGate ((getG ff).[g]) (a, b)).


op garbMap(x:tokens, f:bool functGen, g:int) : token*token*token*token =
  garbleGate x (getG f).[g] (getA f).[g] (getB f).[g] g.

op choose(k:(token*token) array, i:bool array, j:int) : token = getTok k j i.[j].

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
    let pp = init2 ((getN f)+(getQ f)) (garbMap x f) in
    let ff = ((getN f), (getM f), (getQ f), (getA f), (getB f), pp) in
    (ff, Array.sub x 0 (getN f), tt),

  op encrypt(k:keyInput, i:input) = init2 (Array.length i) (choose k i),
  
  op decrypt(k:keyOutput, o:outputG) = map lsb o,

  op queryValid(query:query) =
    let query0 = fst query in
    let query1 = snd query in
    Garble.eval (fst query0) (snd query0) = Garble.eval (fst query1) (snd query1) /\
    phi (fst query0) = phi (fst query1) /\
    Array.length (snd query0) = Array.length (snd query1) /\
    Array.length (snd query0) = (getN (fst query1)) /\
    (getN (fst query0)) + (getQ (fst query0)) <= borne.

export Garble.

lemma encrypt_len :
  forall (k:keyInput, i:input),
    Array.length i > 0 =>
    Array.length (encrypt k i) = Array.length i.
proof.
  intros k i hyp.
  delta encrypt.
  simplify.
  apply (init2_length<:token> (length i) (choose k i) _).
  assumption.
save.

lemma extract :
  forall (ar:bool array),
    forall (f:funct, k:int),
      0 <= k /\
      k <= length ar /\
      0 <= (getA f).[k] /\
      0 <= (getB f).[k] /\
      (getA f).[k] < k /\
      (getB f).[k] < k =>
      extract f k ar = extract f k (sub ar 0 k).
proof.
  intros ar f k h.
  trivial.
save.
  
lemma extractG :
  forall (ar:token array),
    forall (f:functG, k:int),
      0 <= k /\
      k <= length ar /\
      0 <= (getA f).[k] /\
      0 <= (getB f).[k] /\
      (getA f).[k] < k /\
      (getB f).[k] < k =>
      extractG f k ar = extractG f k (sub ar 0 k).
proof.
  intros ar f k h.
  delta extractG.
  simplify.
  trivial.
save.

lemma inverse :
  forall (f : funct) , functCorrect f =>
  forall (x : random) , randomCorrect f x =>
  forall (i : input) , inputCorrect f i =>
    let (g, ki, ko) = garble x f in
    eval f i = decrypt ko (evalG g (encrypt ki i)).
proof. admit. save.
(*
  intros f fC x xC i iC.

  cut introVar : (forall (nn n m q:int) (g:functG) (ig:inputG),
    nn = (getN f) + 1 =>
    n  = getN f =>
    m  = getM f =>
    q  = getQ f =>
    g  = (getN f, getM f, getQ f, getA f, getB f, init2 ((getN f)+(getQ f)) (garbMap x f)) =>
    ig = encrypt (sub x 0 (getN f)) i =>
    let (g, ki, ko) = garble x f in eval f i = decrypt ko (evalG g (encrypt ki i)));
  [|apply (introVar
    ((getN f)+1)
    (getN f)
    (getM f)
    (getQ f)
    (getN f, getM f, getQ f, getA f, getB f, init2 ((getN f)+(getQ f)) (garbMap x f))
    (encrypt (sub x 0 (getN f)) i)
  )].
  intros nn n m q g ig valNN valN valM valQ valG valIG.

  delta eval evalG evalGen garble.
  simplify.
  rewrite <- valG.
  rewrite <- valIG.
  rewrite <- valNN.
  rewrite <- valN.
  rewrite <- valM.
  rewrite <- valQ.

  cut valN2 : (n = (getN g));[trivial|].
  cut valM2 : (m = (getM g));[trivial|].
  cut valQ2 : (q = (getQ g));[trivial|].
  rewrite <- valN2.
  rewrite <- valM2.
  rewrite <- valQ2.
  
  cut main :(forall (j:int), j >= 0 => j < n+q =>
    (appendInit ig (n+q) (extractG g)).[j]
    = getTok x j (appendInit i (n+q) (extract f)).[j]
  ).
    intros jj.
    intros hypJJ1.
    intros hypJJ2.

    delta garble.
    simplify.
    rewrite <- valG.
    rewrite <- valIG.


    apply (strongInduction
      (lambda j, j < n+q =>
        (appendInit ig ((+) n q) (extractG g)).[j]
        = getTok x j (appendInit i ((+) n q) (extract f)).[j])
      _ jj _ _
    );[|trivial|trivial].

    intros j hypJ hypRec hypJ2.
    simplify.
  
    case (j < (getN f)).
    (*Cas de base*)
      intros valJ.
      delta evalGen.
      simplify.
      cut temp : ((appendInit i (n+q) (extract f)).[j] = i.[j]);[trivial|].
      cut tempG : ((appendInit ig (n+q) (extractG g)).[j] = ig.[j]);
      [apply (appendInit_get1<:token> ig (n+q) (extractG g) j _ _);trivial|].
      rewrite temp.
      rewrite tempG.
      rewrite valIG.
      delta encrypt.
      simplify.
      cut cre : ((init2 (length i) (choose (sub x 0 (getN f)) i)).[j] = choose (sub x 0 n) i j);[trivial|].
      rewrite cre.
      delta choose getTok.
      simplify.
      cut sub : ((sub x 0 n).[j] = x.[j]);[trivial|].
      rewrite sub.
      cut test : (j >= 0 /\ j<n+q);[trivial|].
      cut test2 : (lsb (fst x.[j]) <> (lsb (snd x.[j])));[|trivial].
      cut pre : (forall (i:int), 0 <= i => i < n + q =>
        (lsb (getTok x i false)) <> (lsb (getTok x i true)));[trivial|].
    apply (pre j _ _);trivial.
    (*End cas de base*)
    
    (*Induction*)
      intros valJ.
        cut extr : (
        forall (ar1:bool array), forall (ar2:token array), forall (a b:int),
           ar1 = appendInit i (n+q) (extract f) =>
           ar2 = appendInit ig (n+q) (extractG g) =>
           a = (getA f).[j] =>
           b = (getB f).[j] =>
             extractG g j ar2 = getTok x j (extract f j ar1)
      ).
        intros ar1 ar2 a b ar1Val ar2Val aVal bVal.
        delta extract extractG.
        simplify.
        cut hypRecSimpl : (
          forall (k : int),
            k >= 0 => k < j =>
            ar2.[k] = getTok x k ar1.[k]
        ).
          rewrite ar1Val.
          rewrite ar2Val.
          intros k h1 h2.
        apply (hypRec k _ _ _);trivial.

        cut aVal2 : (a = (getA g).[j]);[trivial|].
        cut bVal2 : (b = (getB g).[j]);[trivial|].
        rewrite <- aVal.
        rewrite <- bVal.
        rewrite <- aVal2.
        rewrite <- bVal2.
  
        cut ar2aVal : (ar2.[a] = (getTok x a (fst (ar1.[a], ar1.[b])))).
          rewrite ar2Val.
          rewrite ar1Val.
          apply (hypRec a _ _ _);trivial.
        cut ar2bVal : (ar2.[b] = (getTok x b (snd (ar1.[a], ar1.[b])))).
          rewrite ar2Val.
          rewrite ar1Val.
          apply (hypRec b _ _ _);trivial.
        cut getGVal : ((getG g).[j] = garbleGate x (getG f).[j] a b j);[trivial|].

        rewrite ar2aVal.
        rewrite ar2bVal.
        rewrite getGVal.

        cut fCor : (forall (i:int),
          (getN f) <= i /\ i < (getQ f)+(getN f) =>
            0 <= (getA f).[i] /\ (getA f).[i] < i /\
            0 <= (getB f).[i] /\ (getB f).[i] < i);[trivial|].

      apply (inverse_base (ar1.[a], ar1.[b]) n q m a b j (getG f).[j] x _ _ _ _ _ _ _);
        try split;trivial.

      cut app1 : (forall ex, ex = extract f =>
        (appendInit i (n+q) ex).[j] = ex j (appendInit i (n+q) ex)).
        intros ex exVal.
        apply (appendInit_getFinal<:bool> i (n+q) ex j _ _ _);[trivial|trivial|].
        cut intro : (
          forall ar, ar = appendInit i ((+) n q) ex =>
            ex j ar = ex j (sub ar 0 j)
        ).
          intros ar arVal.
          rewrite exVal.
        apply (extract ar f j _);trivial.
      trivial.
      rewrite (app1 (extract f) _);[trivial|].

      cut app2 : (forall ex, ex = extractG g =>
        (appendInit ig (n+q) ex).[j] = ex j (appendInit ig (n+q) ex)).
        intros ex exVal.
        apply (appendInit_getFinal<:token> ig (n+q) ex j _ _ _);[trivial|trivial|].
        cut intro : (
          forall ar, ar = appendInit ig ((+) n q) ex =>
          ex j ar = ex j (sub ar 0 j)
        ).
          intros ar arVal.
          rewrite exVal.
        apply (extractG ar g j _);trivial.
      trivial.
      rewrite (app2 (extractG g) _);[trivial|].

      apply (extr
        (appendInit i ((+) n q) (extract f))
        (appendInit ig ((+) n q) (extractG g))
        (getA f).[j]
        (getB f).[j]
      ).
    (*End induction*)

  cut lValue : (forall w, 0 <= w /\ w < m =>
    (sub (appendInit i ((+) n q) (extract f)) (n+q-m) m).[w]
     = (appendInit i ((+) n q) (extract f)).[n+q-m+w]
  );[trivial|].
  cut rValue : (forall w, 0 <= w /\ w < m =>
    (map lsb (sub (appendInit ig ((+) n q) (extractG g)) (n+q-m) m)).[w]
    = lsb (appendInit ig ((+) n q) (extractG g)).[n+q-m+w]
  ).
    intros w hypW.
    cut rValue_lem : (
      (sub (appendInit ig ((+) n q) (extractG g)) (n+q-m) m).[w]
      = (appendInit ig ((+) n q) (extractG g)).[n+q-m+w]
    );[trivial|].
  trivial.

  cut main2 :(forall (j:int), j >= n+q-m => j < n+q =>
    (appendInit i (n+q) (extract f)).[j] =
    lsb (appendInit ig (n+q) (extractG g)).[j]).
    intros j hypJ1 hypJ2.
    cut output : (!(lsb (getTok x j false)));[trivial|].
  trivial.

  cut indices : (
    forall (ar1:bool array),
    forall (ar2:bool array),
    length ar1 = length ar2 =>
    (forall i,
      0 <= i /\ i < length ar1 =>
      ar1.[i] = ar2.[i]) =>
    ar1 = ar2
  ).
    intros ar1 ar2 len h.
  apply (extentionality<:bool> ar1 ar2 _);trivial.
  apply (indices
    (sub (appendInit i (n+q) (extract f)) (n+q-m) m)
    (map lsb (sub (appendInit ig (n+q) (extractG g)) (n+q-m) m)) _ _
  );[trivial|].
  intros w hypW.
  rewrite (lValue w _);[trivial|].
  rewrite (rValue w _);[trivial|].
  apply (main2 (n+q-m+w) _ _);trivial.
  save.
*)


module RandGarble : Rand_t = {
  fun gen(f:funct) : random = {
    var i:int;
    var t:bool array;
    var xx : tokens;
    var tok : token;

    i = 0;
    while (i < (getN f)+(getQ f)-(getM f)-1) {
      t.[i] = $Dbool.dbool;
    }
    while (i < (getN f)+(getQ f)-1) {
      t.[i] = false;
    }

    i = 0;
    while (i < (getN f)+(getQ f)-1) {
      tok = $Dkc.genRandKeyLast (! t.[i]);
      xx = setTok xx i true tok;
      tok = $Dkc.genRandKeyLast (t.[i]);
      xx = setTok xx i false tok;
    }
    return xx;
  }
}.
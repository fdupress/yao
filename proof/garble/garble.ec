require import Int.
require import Array.
require import Pair.
require import Bool.

require import CloneDkc.
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
  DKC.decode t aA bB (evalGate ((getG ff).[g]) (a, b)).


op garbMap(x:tokens, f:bool functGen, g:int) : token*token*token*token =
  garbleGate x (getG f).[g] (getA f).[g] (getB f).[g] g.

op choose(k:(token*token) array, i:bool array, j:int) : token = getTok k j i.[j].


op validfx(qu:(bool functGen)*(bool array)) =
  let (n, m, q, aa, bb, gg) = fst qu in
  n > 0 /\ m > 0 /\ q > 0 /\
  length aa = n + q /\ length bb = n + q /\ length gg = n + q /\
  length (snd qu) = n /\
  (range n (n+q-1) true (lambda i b, b /\ aa.[i] >= 0 /\ bb.[i] < i /\ aa.[i] < bb.[i])).

lemma valid_wireinput :
  forall (qu:(bool functGen)*(bool array)),
    validfx qu =>
      let (n, m, q, aa, bb, gg) = fst qu in
      (forall i,
         i >= n  => i < n + q =>
           aa.[i] >= 0 /\
           bb.[i] < i /\
           aa.[i] < bb.[i]).
admit.
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
    let pp = init2 ((getN f)+(getQ f)) (garbMap x f) in
    let ff = ((getN f), (getM f), (getQ f), (getA f), (getB f), pp) in
    (ff, Array.sub x 0 (getN f), tt),

  op encrypt(k:keyInput, i:input) = init2 (Array.length i) (choose k i),
  
  op decrypt(k:keyOutput, o:outputG) = map lsb o,

  op queryValid(query:query) =
    let query0 = fst query in
    let query1 = snd query in
    validfx query0 /\ validfx query1 /\
    Garble.eval (fst query0) (snd query0) = Garble.eval (fst query1) (snd query1) /\
    phi (fst query0) = phi (fst query1) /\
    (getN (fst query0)) + (getQ (fst query0)) <= borne /\
    (getN (fst query1)) + (getQ (fst query1)) <= borne.


export Garble.

lemma encrypt_len :
  forall (k:keyInput, i:input),
    Array.length i > 0 =>
    Array.length (encrypt k i) = Array.length i.
proof.
  delta encrypt.
  progress.
  apply init2_length.
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
      extract f k ar = extract f k (sub ar 0 k) by [].
  
lemma extractG :
  forall (ar:token array),
    forall (f:functG, k:int),
      0 <= k /\
      k <= length ar /\
      0 <= (getA f).[k] /\
      0 <= (getB f).[k] /\
      (getA f).[k] < k /\
      (getB f).[k] < k =>
      extractG f k ar = extractG f k (sub ar 0 k) by (delta extractG;progress;smt).

lemma inverse :
  forall (f : funct) , functCorrect f =>
  forall (x : random) , randomCorrect f x =>
  forall (i : input) , inputCorrect f i =>
    let (g, ki, ko) = garble x f in
    eval f i = decrypt ko (evalG g (encrypt ki i)).
proof.
  intros f hypF x hypX i hypI.

  cut introVar : (forall (nn n m q:int) (g:functG) (ig:inputG),
    nn = (getN f) + 1 =>
    n  = getN f =>
    m  = getM f =>
    q  = getQ f =>
    g  = (getN f, getM f, getQ f, getA f, getB f, init2 ((getN f)+(getQ f)) (garbMap x f)) =>
    ig = encrypt (sub x 0 (getN f)) i =>
    let (g, ki, ko) = garble x f in eval f i = decrypt ko (evalG g (encrypt ki i)));
  [|apply (introVar (*BUG*)
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
  rewrite - valG.
  rewrite - valIG.
  rewrite - valNN.
  rewrite - valN.
  rewrite - valM.
  rewrite - valQ.

  cut valN2 : (n = (getN g));[smt|].
  cut valM2 : (m = (getM g));[smt|].
  cut valQ2 : (q = (getQ g));[smt|].
  rewrite - valN2.
  rewrite - valM2.
  rewrite - valQ2.
  
  cut main :(forall (j:int), j >= 0 => j < n+q =>
    (appendInit ig (n+q) (extractG g)).[j]
    = getTok x j (appendInit i (n+q) (extract f)).[j]
  ).
    intros jj.
    intros hypJJ1.
    intros hypJJ2.

    delta garble.
    simplify.
    rewrite - valG.
    rewrite - valIG.

 (*BUG*)
    apply (Induction.strongInduction
      (lambda j, j < n+q =>
        (appendInit ig ((+) n q) (extractG g)).[j]
        = getTok x j (appendInit i ((+) n q) (extract f)).[j])
      _ jj _ _
    );[|smt|smt].

    intros j hypJ hypRec hypJ2.
    simplify.
  
    case (j < (getN f)).
    (*Cas de base*)
      intros valJ.
      delta evalGen.
      simplify.
      cut temp : ((appendInit i (n+q) (extract f)).[j] = i.[j]);[smt|].
      cut tempG : ((appendInit ig (n+q) (extractG g)).[j] = ig.[j]);
      [apply appendInit_get1;smt|].
      rewrite temp.
      rewrite tempG.
      rewrite valIG.
      delta encrypt.
      simplify.
      cut cre : ((init2 (length i) (choose (sub x 0 (getN f)) i)).[j] = choose (sub x 0 n) i j);[smt|].
      rewrite cre.
      delta choose getTok.
      simplify.
      cut sub : ((sub x 0 n).[j] = x.[j]);[smt|].
      rewrite sub.
      cut test : (j >= 0 /\ j<n+q);[smt|].
      cut test2 : (lsb (fst x.[j]) <> (lsb (snd x.[j])));[|smt].
      cut pre : (forall (i:int), 0 <= i => i < n + q =>
        (lsb (getTok x i false)) <> (lsb (getTok x i true)));[smt|].
    apply (pre j _ _);smt. (*BUG*)
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
        apply hypRec;smt.

        cut aVal2 : (a = (getA g).[j]);[smt|].
        cut bVal2 : (b = (getB g).[j]);[smt|].
        rewrite - aVal.
        rewrite - bVal.
        rewrite - aVal2.
        rewrite - bVal2.
  
        cut ar2aVal : (ar2.[a] = (getTok x a (fst (ar1.[a], ar1.[b])))).
          rewrite ar2Val.
          rewrite ar1Val.
          apply (hypRec a _ _ _);smt. (*BUG*)
        cut ar2bVal : (ar2.[b] = (getTok x b (snd (ar1.[a], ar1.[b])))).
          rewrite ar2Val.
          rewrite ar1Val.
          apply (hypRec b _ _ _);smt. (*BUG*)
        cut getGVal : ((getG g).[j] = garbleGate x (getG f).[j] a b j);[smt|].

        rewrite ar2aVal.
        rewrite ar2bVal.
        rewrite getGVal.

        cut fCor : (forall (i:int),
          (getN f) <= i /\ i < (getQ f)+(getN f) =>
            0 <= (getA f).[i] /\ (getA f).[i] < i /\
            0 <= (getB f).[i] /\ (getB f).[i] < i);[smt|].

(*GROS BUG*) admit. (*
      apply (inverse_base (ar1.[a], ar1.[b]) n q m a b j (getG f).[j] x _ _ _ _ _ _ _);
        try split;smt.*)

      cut app1 : (forall ex, ex = extract f =>
        (appendInit i (n+q) ex).[j] = ex j (appendInit i (n+q) ex)).
        intros ex exVal.
        apply appendInit_getFinal;[smt|smt|].
        cut intro : (
          forall ar, ar = appendInit i ((+) n q) ex =>
            ex j ar = ex j (sub ar 0 j)
        ).
          intros ar arVal.
          rewrite exVal.
        apply extract;smt.
      smt.
      rewrite (app1 (extract f) _);[smt|].

      cut app2 : (forall ex, ex = extractG g =>
        (appendInit ig (n+q) ex).[j] = ex j (appendInit ig (n+q) ex)).
        intros ex exVal.
        apply appendInit_getFinal;[smt|smt|].
        cut intro : (
          forall ar, ar = appendInit ig ((+) n q) ex =>
          ex j ar = ex j (sub ar 0 j)
        ).
          intros ar arVal.
          rewrite exVal.
        apply extractG;smt.
      smt.
      rewrite (app2 (extractG g) _);[smt|].

      apply (extr (*BUG*)
        (appendInit i ((+) n q) (extract f))
        (appendInit ig ((+) n q) (extractG g))
        (getA f).[j]
        (getB f).[j]
      ).
    (*End induction*)

  cut lValue : (forall w, 0 <= w /\ w < m =>
    (sub (appendInit i ((+) n q) (extract f)) (n+q-m) m).[w]
     = (appendInit i ((+) n q) (extract f)).[n+q-m+w]
  );[smt|].
  cut rValue : (forall w, 0 <= w /\ w < m =>
    (map lsb (sub (appendInit ig ((+) n q) (extractG g)) (n+q-m) m)).[w]
    = lsb (appendInit ig ((+) n q) (extractG g)).[n+q-m+w]
  ).
    intros w hypW.
    cut rValue_lem : (
      (sub (appendInit ig ((+) n q) (extractG g)) (n+q-m) m).[w]
      = (appendInit ig ((+) n q) (extractG g)).[n+q-m+w]
    );[smt|].
  smt.

  cut main2 :(forall (j:int), j >= n+q-m => j < n+q =>
    (appendInit i (n+q) (extract f)).[j] =
    lsb (appendInit ig (n+q) (extractG g)).[j]).
    intros j hypJ1 hypJ2.
    cut output : (!(lsb (getTok x j false)));[smt|].
  smt.

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
  apply extensionality;smt.
  apply indices;[smt|]. (*STRANGE
  apply (indices
    (sub (appendInit i (n+q) (extract f)) (n+q-m) m)
    (map lsb (sub (appendInit ig (n+q) (extractG g)) (n+q-m) m)) _ _
  );[smt|].*)
  intros w hypW.
  rewrite (lValue w _);[smt|].
  rewrite (rValue w _);[smt|].
  admit.
(*GROS BUG
  apply (main2 (n+q-m+w) _ _);smt.*)
  save.


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
      tok = $DKC.genRandKeyLast (! t.[i]);
      xx = setTok xx i true tok;
      tok = $DKC.genRandKeyLast (t.[i]);
      xx = setTok xx i false tok;
      i = i + 1;
    }
    return xx;
  }
}.

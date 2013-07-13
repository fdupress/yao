require import Int.
require import Array.
require import Pair.
require import Bool.

require import MyTools.
require import GarbleTools.

require import PreProof.

lemma encrypt_len :
  forall (k:keyInput, i:input),
    Array.length i > 0 =>
    Array.length (encrypt k i) = Array.length i.
proof.
  simplify encrypt=> ? ? ?.
  apply init_length;smt.
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
      extractG f k ar = extractG f k (sub ar 0 k)
by (delta extractG;progress;smt).

lemma correct : 
(forall (t k1 k2 m:Dkc.t),
    DKC.decode t k1 k2 (DKC.encode t k1 k2 m) = m) =>
forall (f : funct) (x : random) (i : input),
 functCorrect f =>
 randomCorrect f x =>
 inputCorrect f i =>
    let (g, ki, ko) = garble x f in
    eval f i = decrypt ko (evalG g (encrypt ki i)).
proof.
  intros DKCHyp.
  intros f hypF x hypX i hypI.
  elimT tuple3_ind (garble x f)=> g ki ko h.
  delta eval evalG evalGen garble.
  simplify.

(*TODO*)

  cut introVar : (forall (nn n m q:int) (g:functG) (ig:inputG),
    nn = (getN f) + 1 =>
    n  = getN f =>
    m  = getM f =>
    q  = getQ f =>
    g  = (getN f, getM f, getQ f, getA f, getB f, init ((getN f)+(getQ f)) (garbMap x f)) =>
    ig = encrypt (sub x 0 (getN f)) i =>
    let (g, ki, ko) = garble x f in eval f i = decrypt ko (evalG g (encrypt ki i)));
  [|apply (introVar (*BUG*)
    ((getN f)+1)
    (getN f)
    (getM f)
    (getQ f)
    (getN f, getM f, getQ f, getA f, getB f, init ((getN f)+(getQ f)) (garbMap x f))
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
require import Int.
require import Array.
require import Pair.
require import Bool.

require import MyTools.
require import GarbleTools.

require import PreProof.

lemma encrypt_len (k:keyInput) (i:input):
  0 < Array.length i =>
  Array.length (encrypt k i) = Array.length i.
proof strict.
by intros=> leq0_len; rewrite /encrypt /= init_length //; first smt.
qed.

(*
lemma extract :
  forall (ar:bool array),
    forall (f:funct, k:int), let k = k + 1 in
      0 < k /\
      k <= length ar /\
      0 <= (getA f).[k] /\
      0 <= (getB f).[k] /\
      (getA f).[k] < k /\
      (getB f).[k] < k =>
      extract f k ar = extract f k (sub ar 0 (k-1)) by [].
  
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
by (delta extractG;progress;smt).*)

(** begin correctionLemma *)
lemma correct:
  (forall (t k1 k2 m:Dkc.t), Dkc.DKC.decode t k1 k2 (Dkc.DKC.encode t k1 k2 m) = m) =>
  forall (f : funct) (x : random) (i : input),
    functCorrect f =>
    randomCorrect f x =>
    inputCorrect f i =>
      let (g, ki, ko) = garble x f in
      eval f i = decrypt ko (evalG g (encrypt ki i)).
(** end correctionLemma *)
proof strict.
  intros DKCHyp.
  intros f x i.

  elimT tuple3_ind (garble x f)=> g ki ko.
  elim/tuple6_ind f=> n' m' q' A' B' F' fVal.
  elim/tuple6_ind g=> n m q A B F gVal.

  simplify eval evalG evalGen garble getN getM getQ randomCorrect tokenCorrect functCorrect garble inputCorrect.
  rewrite valid_wireinput.
  progress.

  pose n := length i.

  pose ki := (sub x 0 n).

timeout 20.

  cut lengthEval : length (evalComplete g (encrypt ki i) extractG) = n + q.
    simplify evalComplete.
    rewrite appendInit_length;first smt.
    rewrite encrypt_len;first smt.
    rewrite gVal.
    simplify getQ.
    smt.

  cut lengthEval2 : length (evalComplete f i extract) = n + q.
    simplify evalComplete.
    rewrite appendInit_length;first smt.
    rewrite fVal.
    simplify getQ.
    smt.
  rewrite /n -fVal -/n.
  
  cut -> : (n, m, q, getA f, getB f, init (n + q) (garbMap x f)) = g by smt.

  cut main : (forall (j:int), 0 <= j < n+q =>
    (evalComplete g (encrypt ki i) extractG).[j]
    = getTok x j (evalComplete f i extract).[j]
  );first last.

    apply extensionality.
    cut len : (length (sub (evalComplete f i extract) (n + q - m) m) =
      length (decrypt tt (sub (evalComplete g (encrypt ki i) extractG) (n + q - m) m))).
      simplify decrypt.
      rewrite sub_length;first 3 smt.
      smt.
    split;first smt.
    intros k kmin kmax.
    cut km : length (sub (evalComplete f i extract) (n + q - m) m) = m by smt.
    rewrite sub_get;first 5 smt.
    simplify decrypt.
    rewrite map_get;first 2 smt.
    rewrite sub_get;first 5 smt.
    rewrite main;first smt.
    generalize ((evalComplete f i extract).[k + (n + q - m)])=> b.
    case b;
      (cut := H9 (k + (n+q-m)) _ _;first 2 smt);
      (cut := H10 (k + (n+q-m)) _ _;first 2 smt);
      smt.

  intros j boundJ.
  cut : j < n + q;first smt.
  elim/ Induction.strongInduction j;last smt.
  intros k kPos hypRec kbound.
  simplify evalComplete.
  case (k < n)=> hyp;
    first by (rewrite ! appendInit_get1;first 4 smt);
             simplify encrypt choose getTok;
             rewrite init_get;smt.
  cut hh := H7 k.
  cut h : (getA g) = A' by smt.
  cut := hypRec (getA g).[k] _ _;first 2 rewrite h;clear h;smt.
  clear h.
  cut h : (getB g) = (getB f) by smt.
  cut := hypRec (getB g).[k] _ _;first 2 rewrite h;clear h;smt.
  clear h hh.

  cut hhhhh : extractG g (k - 1) (appendInit (encrypt ki i) (getQ g) (extractG g)) =
extractG g (k - 1)
  (sub (appendInit (encrypt ki i) (getQ g) (extractG g)) 0 k).
    pose ar := ((appendInit (encrypt ki i) (getQ g) (extractG g))).
    delta extractG;progress.
    rewrite ! sub_get;smt.

cut hhhhhh : 
extract f (k - 1) (appendInit i (getQ f) (extract f)) =
extract f (k - 1) (sub (appendInit i (getQ f) (extract f)) 0 k).
    pose ar := ((appendInit i (getQ f) (extract f))).
    delta extract;progress.
    rewrite ! sub_get;smt.

cut h : length (encrypt ki i) = n by smt.
cut hh : getQ g = q by smt.
  rewrite appendInit_getFinal;first 3 smt.
  rewrite appendInit_getFinal;first 3 smt.
rewrite {3} /extractG.
rewrite {3} /extract.
simplify evalComplete.
generalize ((appendInit (encrypt ki i) (getQ g) (extractG g)))=> X.
generalize (appendInit i (getQ f) (extract f))=> Y.
cut -> : k - 1 + 1 = k by smt.
intros -> ->.
cut -> : (getG g) = init (n + q) (garbMap x (n, m, q, A', B', F')) by smt.
rewrite init_get;first 2 smt.
simplify garbMap.
cut -> : (n, m, q, A', B', F') = f by smt.
cut -> : (getA f = getA g) by smt.
cut -> : (getB f = getB g) by smt.
pose a := (getA g).[k].
pose b := (getB g).[k].
pose i1 := (Y.[a]).
pose i2 := (Y.[b]).
  cut hhh := H7 k.
cut hhhh : (getA g) = A' by smt.
cut hhhh2 : (getB g) = B' by smt.
apply (inverse_base _ i1 i2 n q m (getA g).[k] (getB g).[k] k ((getG f).[k]) x _ _ _ _ _ _ _)=> //.
smt.
smt.
smt.
smt.
simplify tokenCorrect;smt.
save.
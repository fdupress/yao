require import Int.
require import Array.
require import Logic.

op init2: int -> (int -> 'a) -> 'a array.

axiom init2_length: forall (n:int, f:int -> 'a), n > 0 =>
  length (init2 n f) = n.

axiom init2_get: forall (n:int, i:int, f:int -> 'a),
  0 <= i => i < n =>
  (init2 n f).[i] = f i.

  
op range : int -> int -> 'a -> (int -> 'a -> 'a) -> 'a.

axiom range_init :
  forall (i j:int),
    forall (x:'a),
      forall (f:int -> 'a -> 'a),
        j <= i => range i j x f = x.

axiom range_ind :
  forall (i j:int),
    forall (x:'a),
      forall (f:int -> 'a -> 'a),
        i < j => (range i j x f = f (j-1) (range i (j-1) x f)).

op appender(extract:int -> 'a array ->  'a, i:int, ar:'a array) : 'a array =
  ar:::(extract (i-1) ar).

op appendInit(ar:'a array, size:int, extract:int -> 'a array -> 'a) : 'a array =
  let n = Array.length ar in
  range n (n+size) ar (appender extract).

lemma appendInit_length :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    n >= 0 =>
    Array.length (appendInit ar n extract) = (Array.length ar) + n.
proof.
  intros ar n extract hypN.
  apply (
    Induction.induction
    (lambda (l:int), l <= n =>
      (Array.length (appendInit ar l extract) = (Array.length ar) + l))
    _ _ n _ _);[smt| |smt|smt].
    intros j hypj hypRec hypJ2.
    cut hyp : ((length ar) + j = length (appendInit ar (j-1) extract) + 1);[smt|].
    rewrite hyp.
    delta appendInit.
    simplify.
    cut temp : (
      (range (length ar) ((+) (length ar) j) ar (appender extract)) = appender extract ((+) (length ar) j) (range (length ar) ((+) (length ar) ((-) j 1)) ar (appender extract)));smt.
save.


lemma appendInit_ind :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      0 <= k /\ k < (Array.length ar) + n - 1 =>
      n > 0 =>
      (appendInit ar n extract).[k] = (appendInit ar (n-1) extract).[k].
proof.
  intros ar n extract k hypK hypN.
  cut introVar : (
     forall s,
       s = (length ar)=>
         (appendInit ar n extract).[k] = (appendInit ar ((-) n 1) extract).[k]
  );[|smt].
  intros s valS.
  delta appendInit.
  simplify.
  rewrite - valS.
  cut lem : (
    (range s (s+n) ar (appender extract)) =
    (appender extract (s+n) (range s ((s+n)-1) ar (appender extract)))
  );smt.
save.

lemma appendInit_get1 :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      0 <= k /\ k < Array.length ar =>
      n >= 0 =>
      (appendInit ar n extract).[k] = ar.[k].
proof.
  intros ar n extract k hypK hypN.
  apply (
    Induction.induction
    (lambda (l:int), l <= n => (appendInit ar l extract).[k] = ar.[k])
    _ _ n _ _);smt.
save.


lemma appendInit_get2 :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      Array.length ar <= k /\ k < (Array.length ar) + n - 1 =>
      n > 0 =>
      (appendInit ar n extract).[k] = (extract k (appendInit ar (k-length ar) extract)).
proof.
  intros ar n extract k hypK hypN.
  rewrite (_: n = ((k-length ar)+1+(n-(k-length ar)-1)));[smt|].
  apply (Induction.induction
    (lambda i, (appendInit ar ((k-length ar)+1+i) extract).[k] = (extract k (appendInit ar (k-length ar) extract)))
    _ _ (n-(k-length ar)-1) _
  );[|smt|smt].
  simplify.
  cut lem : ((appendInit ar (k-(length ar)+1) extract)
    = appender extract (k+1) (appendInit ar (k-(length ar)) extract)
  );smt.
save.

lemma appendInit_getFinal :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      Array.length ar <= k /\ k < (Array.length ar) + n - 1 =>
      n > 0 =>
      extract k (appendInit ar n extract) = extract k (sub (appendInit ar n extract) 0 k) =>
      (appendInit ar n extract).[k] = (extract k (appendInit ar n extract)).
proof.
  intros ar n extract k hypK hypN hypExtract.
  cut temp : ((appendInit ar n extract).[k] = (extract k (appendInit ar (k-length ar) extract)));[smt|].
  rewrite temp.
  cut temp2 : (sub (appendInit ar n extract) 0 k = appendInit ar (k-(length ar)) extract);[|smt].
  cut temp3 : (forall i, 0 <= i /\ i < k => (appendInit ar (k-(length ar)) extract).[i] = (appendInit ar n extract).[i]).
    intros i hypI.
    rewrite (_: n = ((+) ((-) n ((-) k (length ar))) ((-) k (length ar))) );[smt|].
    apply (Induction.induction
      (lambda j,
        j <= n - ((-) k (length ar)) =>
        (appendInit ar ((-) k (length ar)) extract).[i] =
          (appendInit ar (j+((-) k (length ar))) extract).[i]
      ) _ _ (n - ((-) k (length ar))) _ _
    );smt.
  apply (extensionality<:'a> (sub (appendInit ar n extract) 0 k) (appendInit ar ((-) k (length ar)) extract) _ );smt.
save.

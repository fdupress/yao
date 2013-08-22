require import Int.
require import Array.

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
    0 <= n =>
    Array.length (appendInit ar n extract) = (Array.length ar) + n.
proof.
intros ? ? ? ?.
pose m := n.
cut : (m <= n) by smt.
elim/Induction.induction m;[smt| |smt].
intros=> /= j ? ? ?.
rewrite /appendInit /=.
rewrite range_ind /=;first smt.
rewrite /appender.
rewrite snoc_length.
rewrite (_:length ar + (j + 1)- 1 = length ar + j);first smt.
smt.
save.


lemma appendInit_ind :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      0 <= k /\ k < (Array.length ar) + n - 1 =>
      n > 0 =>
      (appendInit ar n extract).[k] = (appendInit ar (n-1) extract).[k].
proof.
  intros ? ? ? ? ? ?.
  simplify appendInit.
  rewrite range_ind;smt.
save.

lemma appendInit_get1 :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      0 <= k /\ k < Array.length ar =>
      n >= 0 =>
      (appendInit ar n extract).[k] = ar.[k].
proof.
intros ? ? ? ? ? ?.
pose m := n.
cut : (m <= n);first smt.
elim/Induction.induction m;smt.
save.


lemma appendInit_get2 :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      Array.length ar <= k /\ k < (Array.length ar) + n - 1 =>
      n > 0 =>
      (appendInit ar n extract).[k] = (extract (k-1) (appendInit ar (k-length ar) extract)).
proof.
  intros ? ? ? ? ? ?.
  rewrite (_: n = ((k-length ar)+1+(n-(k-length ar)-1)));[smt|].
  elim/Induction.induction (n-(k-length ar)-1);[|smt|smt].
  simplify appendInit.
  rewrite (_:length ar + (k - length ar + 1) = k + 1);first smt.
  rewrite (_:length ar + (k - length ar) = k);first smt.
  rewrite range_ind;first smt.  
  rewrite (_:k + 1 - 1 = k);first smt.
  cut h : (length (range (length ar) k ar (appender extract)) = k).
    admit.
  generalize h.
  generalize (range (length ar) k ar (appender extract))=> xs h.
  simplify appender.
  rewrite snoc_get;smt.
save.

lemma appendInit_getFinal :
  forall (ar:'a array) (n:int) (extract:int -> 'a array -> 'a),
    forall (k:int),
      Array.length ar <= k /\ k < (Array.length ar) + n - 1 =>
      n > 0 =>
      extract k (appendInit ar n extract) = extract k (sub (appendInit ar n extract) 0 k) =>
      (appendInit ar n extract).[k] = (extract (k-1) (appendInit ar n extract)).
proof.
  intros ar n extract k hypK hypN hypExtract.
  
  cut temp : ((appendInit ar n extract).[k] = (extract (k-1) (appendInit ar (k-length ar) extract)));[smt|].
  rewrite temp.
  cut temp2 : (sub (appendInit ar n extract) 0 k = appendInit ar (k-(length ar)) extract).
  cut temp3 : (forall i, 0 <= i /\ i < k => (appendInit ar (k-(length ar)) extract).[i] = (appendInit ar n extract).[i]).
    intros i hypI.
    rewrite (_: n = ((+) ((-) n ((-) k (length ar))) ((-) k (length ar))) );[smt|].
    pose b := n - ((-) k (length ar)).
    pose j := b.
    cut : (j <= b) by smt.
    elim/Induction.induction j;smt.
  apply extensionality;smt.
  rewrite - temp2.
  admit.
save.

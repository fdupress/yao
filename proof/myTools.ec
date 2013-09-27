require import Int.
require import Array.

op range : int -> int -> 'a -> (int -> 'a -> 'a) -> 'a.

axiom range_init (i j:int) (x:'a) (f:int -> 'a -> 'a):
  j <= i => range i j x f = x.

axiom range_ind (i j:int) (x:'a) (f:int -> 'a -> 'a):
  i < j => (range i j x f = f (j-1) (range i (j-1) x f)).

op appender (extract:int -> 'a array ->  'a) (i:int) (ar:'a array) : 'a array =
  ar:::(extract (i-1) ar).

op appendInit (ar:'a array) (size:int) (extract:int -> 'a array -> 'a) : 'a array =
  let n = Array.length ar in
  range n (n+size) ar (appender extract).

lemma appendInit_length (ar:'a array) (n:int) (extract:int -> 'a array -> 'a):
  0 <= n =>
  Array.length (appendInit ar n extract) = (Array.length ar) + n.
proof strict.
intros=> leq0_n.
pose m:= n; cut : m <= n by smt.
elim/Induction.induction m; [smt | | smt].
intros=> i leq0_i IH leqi1_n.
rewrite /appendInit /= range_ind /=; first smt.
rewrite /appender snoc_length; smt.
qed.

lemma appendInit_ind (ar:'a array) (n:int) (extract:int -> 'a array -> 'a) (k:int):
  0 <= k < (Array.length ar) + n - 1 =>
  0 < n =>
  (appendInit ar n extract).[k] = (appendInit ar (n-1) extract).[k].
proof strict.
by intros=> [leq0_k ltk_len] lt0_n;
   rewrite /appendInit /= range_ind; smt.
qed.

lemma appendInit_get1 (ar:'a array) (n:int) (extract:int -> 'a array -> 'a) (k:int):
  0 <= k < Array.length ar =>
  0 <= n =>
  (appendInit ar n extract).[k] = ar.[k].
proof strict.
intros=> [leq0_k ltk_len] leq0_n.
pose m := n; cut :m <= n; first smt.
elim/Induction.induction m; smt.
qed.

lemma appendInit_get2 (ar:'a array) (n:int) (extract:int -> 'a array -> 'a) (k:int):
  Array.length ar <= k < (Array.length ar) + n =>
  0 < n =>
  (appendInit ar n extract).[k] = (extract (k - 1) (appendInit ar (k - length ar) extract)).
proof strict.
intros=> [leqlen_k lt_k_len] lt0_n.
cut ->: n = (k - length ar) + 1 + (n - (k - length ar) - 1) by smt.
elim/Induction.induction (n - (k - length ar) - 1); last 2 smt.
rewrite /appendInit /=.
cut ->: length ar + (k - length ar + 1) = k + 1 by smt.
cut ->: length ar + (k - length ar) = k by smt.
rewrite range_ind; first smt.
cut ->: k + 1 - 1 = k by smt.
cut :length (appendInit ar (k - length ar) extract) = k; smt.
qed.

lemma appendInit_getFinal (ar:'a array) (n:int) (extract:int -> 'a array -> 'a) (k:int):
  Array.length ar <= k < (Array.length ar) + n =>
  0 < n =>
  extract (k-1) (appendInit ar n extract) = extract (k-1) (sub (appendInit ar n extract) 0 k) =>
  (appendInit ar n extract).[k] = (extract (k-1) (appendInit ar n extract)).
proof strict.
intros=> [leqlen_k ltk_len lt0_n] hypExtract.
cut ->:= appendInit_get2 ar n extract k _ _=> //.
rewrite hypExtract.
cut ->: sub (appendInit ar n extract) 0 k = appendInit ar (k - length ar) extract; last by reflexivity.
apply extensionality; split.
  by rewrite sub_length; smt.
  by intros=> i leq0_i; rewrite sub_length; smt.
qed.

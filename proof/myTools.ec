require import Int.
require import Array.

op range (i j:int) (base:'a) (f:int -> 'a -> 'a) : 'a =
  if j <= i then base else
  fold_left (lambda state x, f x state) base (Array.init (j-i) (lambda x, (j-1)-x)).

lemma range_init (i j:int) (x:'a) (f:int -> 'a -> 'a):
  j <= i => range i j x f = x by smt.

lemma range_ind (i j:int) (x:'a) (f:int -> 'a -> 'a):
  i < j => (range i j x f = f (j-1) (range i (j-1) x f)).
proof strict.
intros h.
simplify range.
cut -> : j <= i = false by smt.
simplify.
rewrite fold_left_cons /=;first smt.
rewrite get_init /=;first smt.
case (j - 1 <= i)=> hh;first smt.
do 2 ! congr=> //.
apply array_ext;smt.
qed.

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
rewrite /appender length_snoc; smt.
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
apply array_ext; split.
  by rewrite length_sub; smt.
  by intros=> i leq0_i; rewrite get_sub; smt.
qed.

(** Auxiliary definitions for garbling schemes *)

require import Bool.
require import Int.
require import Array.
require import IntDiv.
require import IntExtra.
require import FSet.
require import NewFMap.
require import Pair.

require import ArrayExt.

theory ForLoop.

  op range: int -> int -> 'a -> (int -> 'a -> 'a) -> 'a.

  axiom range_base i j (st:'a) f:
    Int.( <= ) j i =>
    range i j st f = st.

  axiom range_ind i j (st:'a) f:
    Int.( < ) i j =>
    range i j st f = range (i + 1) j (f i st) f.

  lemma range_ind_lazy i j (st:'a) f:
    Int.( < ) i j =>
    range i j st f = f (j - 1) (range i (j - 1) st f).
  proof.
    move=> h; cut {h}: 0 < j-i by smt full.    
    move: {-1}(j-i) (Logic.eq_refl (j - i))=> n.
    move=> eq_iBj_n gt0_n; move : i j eq_iBj_n.
    cut ge0_n: 0 <= n by smt full.
    move : ge0_n gt0_n st.
    elim/intind n; first smt full.
    move=> n ge0_n IH _ st i j.
    case (n = 0); first move=> -> h.
      cut ->: j = i+1 by smt full.
      rewrite range_ind ?range_base; 2..4:smt.
      smt full.
    move=> nz_n eq_iBj_Sn; rewrite range_ind; first by smt full.
    rewrite IH; [smt full|smt|].
    congr => //.
    by rewrite -range_ind; first smt full.
  qed.

  (* General result on boolean accumulation *)
  lemma rangeb_forall i j p b:
    ForLoop.range i j b (fun k b, b /\ p k) =
     (b /\ forall k, i <= k <= j-1 => p k).
  proof.
    case (i < j)=> i_j; last smt full.
    pose n := j - i; cut ->: j = n + i by smt.
    cut: 0 <= n by smt full.
    elim/intind n; first by smt.
    move => i0 Hi0 Hrec;rewrite range_ind_lazy; first by smt.
    simplify. 
    cut ->: i0 + 1 + i - 1 = i0 + i by smt.
    rewrite Hrec.
    by case ((b /\ forall (k : int), i <= k <= i0 + i - 1 => p k)); smt.
  qed.

  (* General result on restricting the range *)
  lemma range_restr (i j:int) (base:'a) f:
    0 <= j - i =>
    ForLoop.range i j base (fun k a, if i <= k < j then f k a else a) = ForLoop.range i j base f.
  proof.
    move=> h; case (0 = j - i)=> h2; first smt full.
    pose k:= j - i - 1; cut {1 3}->: j = k + i + 1 by smt.
    cut: k < j - i by smt full.
    cut: 0 <= k by smt full.
    elim/intind k; first by smt.
    move => i0 ge0_i0 Hind Hi0j.
    rewrite range_ind_lazy; first by smt.
    simplify.
      cut ->: i <= i0 + 1 + i + 1 - 1 < j <=> true by smt. 
      by simplify; smt.
  qed.

  axiom range_add i j1 j2 (a:'a) f : 0 <= j1 => 0 <= j2 => i <= j1 =>
    range i (j1 + j2) a f = range (i+j1) (j1 + j2) (range i j1 a f) f.
end ForLoop.

lemma nosmt strongInduction (p:int -> bool):
  (forall j, 0 <= j => (forall k, 0 <= k < j => p k) => p j) =>
  (forall i, 0 <= i => p i).
proof.
  move => hyp i iVal.
  apply (intind (fun i, forall k, 0 <= k <= i => p k) _ _ i); 1..2:(smt full); smt.
qed.

(** appender operation *)
(**
  The appender operation appends at the end of some given array
  a value of that array.
*)
op appender (extract:int->'a array->'a) (i:int) (ar:'a array): 'a array =
  ar:::(extract (i-1) ar).

(** appendInit operation *)
(**
  The appendInit operation appends a range of values of some
  given array to the end of that array.
*)
op appendInit (ar:'a array) (size:int) (extract:int->'a array->'a):'a array =
  let n = Array.size ar in
  ForLoop.range n (n+size) ar (appender extract).

(** 
  Size of the output array of appendInit: size of the original
  array plus the number of elements appended to it.
*)
lemma appendInit_size (ar:'a array) (n:int) (extract:int->'a array->'a):
  0 <= n =>
  Array.size (appendInit ar n extract) = (Array.size ar) + n.
proof.
  move=> leq0_n.
  pose m:= n.
  cut: 0 <= m by smt.
  elim/intind m; first smt.
  move => i Hi IH /=. 
  rewrite /appendInit /= ForLoop.range_ind_lazy /=; first by smt.
  rewrite addzA.
  cut ->: size ar + i + 1 - 1 = size ar + i by smt.
  by rewrite -IH; smt.
qed.

(** Values of appendInit *)
(**
  Inductive definition of the values: the values of two 
  appendInit arrays are equal until the size of the smaller
  array.
*)
lemma appendInit_ind (ar:'a array) (n:int) (extract:int->'a array->'a) (k:int):
  0 <= k < (Array.size ar) + n - 1 =>
  0 < n =>
  (appendInit ar n extract).[k] = (appendInit ar (n-1) extract).[k].
proof.
  move => [leq0_k ltk_len] lt0_n.
  rewrite /appendInit /=.
  rewrite ForLoop.range_ind_lazy; first by idtac=>/#. 
  cut ->: ForLoop.range (size ar) (size ar + (n - 1)) ar (appender extract) = appendInit ar (n-1) (extract) by rewrite /appendInit /=. 
  by smt.
qed.

(**
  If the index is lower than the size of the original array,
  then the value in the resulting array is the same of the
  original array.
*)
lemma appendInit_get1 (ar:'a array) (n:int) (extract:int->'a array->'a) (k:int):
  0 <= k < Array.size ar =>
  0 <= n =>
  (appendInit ar n extract).[k] = ar.[k].
proof.
  move=> [leq0_k ltk_len] leq0_n.
  pose m := n; cut: 0 <= m by smt.
  by elim/intind m; smt.
qed.

(**
  If the index is greater than the size of the original array,
  then the value in the resulting array is the same of the 
  value of the symmetric of the index in the original array, 
  considering as "zero" the size of the original array.
*)
lemma appendInit_get2 (ar:'a array) (n:int) (extract:int->'a array->'a) (k:int):
  Array.size ar <= k < (Array.size ar) + n =>
  0 < n =>
  (appendInit ar n extract).[k] = (extract (k - 1) (appendInit ar (k - size ar) extract)).
proof.
  move=> [leqlen_k lt_k_len] lt0_n.
  cut ->: n = (k - size ar) + 1 + (n - (k - size ar) - 1) by smt.
  cut: 0 <= (n - (k - size ar) - 1) by smt.
  elim/intind (n - (k - size ar) - 1).
    rewrite /appendInit /=.
    cut ->: size ar + (k - size ar + 1) = k + 1 by smt.
    cut ->: size ar + (k - size ar) = k by smt.
    rewrite ForLoop.range_ind_lazy; first smt.
    cut ->: k + 1 - 1 = k by smt. 
    cut hk : k = size (appendInit ar (k - size ar) extract) by smt.
    rewrite hk ?appendInit_size; first by smt.
    cut ->: size ar + (k - size ar) = k by smt.
    by rewrite hk; smt. 
    move => i ige0 Hind; rewrite -Hind.
    by smt timeout=60.
qed.

(**
  If the index is greater than the size of the original array,
  the value in the resulting array is the same of the value indexed
  by the same index in the sub array with the size of the index.
*)
lemma appendInit_getFinal (ar:'a array) (n:int) (extract:int->'a array->'a) (k:int):
  Array.size ar <= k < (Array.size ar) + n =>
  0 < n =>
  extract (k-1) (appendInit ar n extract) = extract (k-1) (sub (appendInit ar n extract) 0 k) =>
  (appendInit ar n extract).[k] = (extract (k-1) (appendInit ar n extract)).
proof.
  move=> [leqlen_k ltk_len lt0_n] hypExtract.
  cut ->:= appendInit_get2 ar n extract k _ _=> //.
  rewrite hypExtract.
  cut ->: sub (appendInit ar n extract) 0 k = appendInit ar (k - size ar) extract; last by reflexivity.
  apply arrayP; split.
    by rewrite size_sub; smt.
    move=> i leq0_i; rewrite get_sub; first 4 by smt. 
    by simplify; smt timeout=30.
qed.

(** Injectivity of appendInit *)
lemma ext_appendInit (q:int) (x:'a array) (extract1 extract2:int -> 'a array -> 'a) :
  0 <= q =>
  (forall g, size x - 1 <= g < size x + q - 1 => extract1 g = extract2 g) =>
  appendInit x q extract1 = appendInit x q extract2.
proof.
  simplify appendInit.
  move => hq h.
  pose j := q.
  cut: j <= q by smt.
  cut: 0 <= j by smt.
  elim/intind j=> //; first smt.
  move => i hi hr H.
  rewrite (ForLoop.range_ind_lazy _ _ _ (appender extract1));first smt.
  rewrite (ForLoop.range_ind_lazy _ _ _ (appender extract2));first smt.
  cut ->: size x + (i + 1) - 1 = size x + i by smt.
  by smt.
qed.

(** evalComplete operation *)
(**
  Same as the appendInit operation.
*)
op evalComplete (q:int) (x:'a array) (extract:int -> 'a array -> 'a): 'a array =
  appendInit x q extract.

(** extract operation *)
(**
  The extract operation evaluates a give function with respect to 
  two values (defined by two arrays of indexes) of some array.

  The extract operation is used to get the evaluation of two wires
  in a given gate. Considering aa the array of all the first input
  wires of every gate, bb the array of all the second input wires
  of every gate, g the gate and x the input of the circuit, aa.[g]
  outputs the first input wire of gate g, bb.[g] outputs the second
  input wire of gate g, x.[aa.[g]] and x.[bb.[g]] outputs the wires
  of the input that correspond to the input wires of the gate and
  eval g x.[aa.[g]] x.[bb.[g]] outputs the evaluation of the gate g
  with respect to the wires defined by x.[aa.[g]] and x.[bb.[g]].
*)
op extract (eval:int -> 'a -> 'a -> 'a) (aa:int array) (bb:int array) (g:int) (x:'a array): 'a =
  let g = g + 1 in
  eval g x.[aa.[g]] x.[bb.[g]].

(** Topology of a circuit *)
(**
  The topology of a circuit is a 5-tuple (n,m,q,A,B):
    - n >= 2 - number of input wires
    - m >= 1 - number of output wires
    - g >= 1 - number of gates
    - A - set of the first input wires of every gate
    - B - set of the second input wires of every gate

  Considering the conventional definition of circuit,
  the topology does not consider the G element, that
  corresponds to the functionality of every gate and,
  therefore, to the functionality of the circuit.
*)
type topo_t = int*int*int*(int array)*(int array).
  
(**
  Tweak theory.
    
  A tweak is a parameter necessary to the definition of
  dual-key cipher encryption schemes. Those are used
  to "adjust" the values of the E permutation and of
  the D permutation.
*)
theory Tweak.

  (** We consider tweaks that are bit strings *)
  require ExtWord.
  clone import ExtWord as WT.

  (** Function that converts a boolean value into
    an integer *)
  op bti (x:bool) = if x then 1 else 0.

  (** Tweak definition *)
  (** 
    A tweak is the bit string representation of some integer value
    that depends on one integer g and two booleans a and b
  *)
  op tweak (g:int) (a:bool) (b:bool) : word = WT.from_int (4 * g + 2 * bti a + bti b).

  lemma pow_base0 (p : int) : 0 < p => 0 ^ p = 0.
  proof. 
    move => Hp.
    cut ->: p = (p-1) + 1 by smt.
    rewrite powS; first by smt.
    by simplify.   
  qed.

  axiom mul_div_frac a b c d : (a * b) %/ (c * d) = (a %/ c) * (b %/ d). 
  
  lemma mult_div_frac x y z : x %/ (y * z) = (x %/ y) * (1 %/ z) by [].
  
  lemma power_div x a b : 0 <= a => 0 <= b => x ^ (a - b) = x ^ a %/ x ^ b.
  proof.
    move => Ha.
    elim/intind b.
    simplify.
    rewrite pow0; first by smt. 
    move => i ige0 Hind.
    rewrite powS; first by exact ige0.
    rewrite mulzC mult_div_frac -Hind.
    by smt timeout=30.
  qed.
  
  (** Bounds of the tweak *)
  lemma nosmt tweak_bounds g a b:
    0 <= g < 2^(WT.length - 2) =>
    0 <= 4 * g + 2 * bti a + bti b <= 2^WT.length - 1.
   proof. 
     case a.
     case b => _ _.
     rewrite /bti /=; progress; first by smt.
     cut ->: 4 * g + 2 + 1 <= 2 ^ WT.length - 1 <=> 4 * g <= 2^WT.length - 4 by smt.
     cut ->: 4 * g <= 2 ^ WT.length - 4 <=> (4 * g) %/ 4 <= (2 ^ WT.length - 4) %/ 4 by smt. 
     rewrite mulzC mulzK; first by trivial. 
     move : H0. rewrite power_div. smt. smt. cut ->: 2 ^ 2 = 4. cut ->: 2^2 = 2^(1+1) by smt. rewrite powS. trivial. by smt. move => Hx. smt full tmo=60.
     move => H.
     rewrite /bti /=. 
     elim H => ge0_g lg.
     split; first by smt.
     move => ge0_4g2.
     cut ->: 4 * g + 2 <= 2 ^ WT.length - 1 <=> 4 * g <= 2 ^ WT.length - 3 by smt.
     cut ->: 4 * g <= 2 ^ WT.length - 3 <=> (4 * g) %/ 4 <= (2 ^ WT.length - 3) %/ 4 by smt.
     by smt full tmo=60.
     progress; rewrite /bti /=; first by smt.
     case b.
       move => b1.
       cut ->: 4 * g + 1 <= 2 ^ WT.length - 1 <=> 4 * g <= 2 ^ WT.length - 2 by smt.
       cut ->: 4 * g <= 2 ^ WT.length - 2 <=> (4 * g) %/ 4 <= (2 ^ WT.length - 2) %/ 4 by smt.
       by smt full tmo=60.
       move => b0.
       cut ->: 4 * g + 0 <= 2 ^ WT.length - 1 <=> 4 * g <= 2 ^ WT.length - 1 by smt.
       cut ->: 4 * g <= 2 ^ WT.length - 1 <=> (4 * g) %/ 4 <= (2 ^ WT.length - 1) %/ 4 by smt.
       by smt full tmo=60.
   qed.
   
  (** Injectivity of the elements that define the tweak *)
  lemma nosmt decomp g g' a a' b b':
    0 <= g =>
    0 <= g' =>
    0 <= a <= 1 =>
    0 <= a' <= 1 =>
    0 <= b <= 1 =>
    0 <= b' <= 1 =>
    4 * g + 2 * a + b = 4 * g' + 2 * a' + b' =>
    g = g' /\ a = a' /\ b = b'
  by [].
      
  (** Injectivity of the tweak *)
  lemma tweak_inj g g' a a' b b':
    0 <= g  < 2 ^ (WT.length - 2) =>
    0 <= g' < 2 ^ (WT.length - 2) =>
    tweak g a b = tweak g' a' b' =>
    g = g' /\ a = a' /\ b = b'.
  proof.
    move=> hg hg'.
    rewrite /tweak=> fi_g_g'.
    cut:= decomp g g' (bti a) (bti a') (bti b) (bti b') _ _ _ _ _ _ _;
      first 6 by smt.
    cut t_bound := tweak_bounds g  a  b _=> //;
      cut t'_bound := tweak_bounds g' a' b' _=> //.
    by apply from_int_inj; smt.
    by smt.
  qed.
end Tweak.
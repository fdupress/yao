(** This is an extension to the EasyCrypt's Array theory with several facts relating
 array distributions, samplings and loops.
*)

require import Option Real Distr NewDistr Int IntExtra List Array Pair DList.
require (*--*) Bigop.

lemma size_ofarray (xs : 'x array) : size (ofarray xs) = size xs by smt.
    
(** Empty *)
op empty : 'x array = mkarray [] axiomatized by emptyE.

lemma size_empty : size (empty<:'x>) = 0. 
proof.
  by rewrite emptyE size_mkarray size_eq0.
qed.
    
lemma empty_unique (xs:'x array):
  size xs = 0 => xs = empty.
proof. 
  by move=> xs_0; apply arrayP; split;
     [rewrite size_empty | smt].
qed.

(** Append *)
op (||) (a1 a2 : 'x array) = mkarray (ofarray a1 ++ ofarray a2) axiomatized by appendE.

lemma size_append (xs0 xs1:'x array):
  size (xs0 || xs1) = size xs0 + size xs1.
proof. 
  by rewrite appendE size_mkarray size_cat ?size_ofarray;
    reflexivity.
qed.

lemma get_append (xs0 xs1:'x array) (i:int):
  0 <= i < size (xs0 || xs1) =>
  (xs0 || xs1).[i] = (0 <= i < size xs0) ? xs0.[i] : xs1.[i - size xs0].
proof. 
  rewrite size_append; move => Hsize. 
  rewrite ?getE.
  rewrite appendE ofarrayK nth_cat.
  case (0 <= i < size xs0) => hc.
    by cut ->: i < size (ofarray xs0) <=> true by smt.
    cut ->: i < size (ofarray xs0) <=> false by smt.
    by rewrite size_ofarray.
qed.  

lemma nosmt get_append_left (xs0 xs1:'x array) (i:int):
 0 <= i < size xs0 =>
 (xs0 || xs1).[i] = xs0.[i]
by [].

lemma nosmt get_append_right (xs0 xs1:'x array) (i:int):
 size xs0 <= i < size xs0 + size xs1 =>
 (xs0 || xs1).[i] = xs1.[i - size xs0]
by [].

lemma set_append (xs0 xs1:'x array) (i:int) x:
  0 <= i < size (xs0 || xs1) =>
  (xs0 || xs1).[i <- x] = (0 <= i < size xs0) ? 
     (xs0.[i <- x] || xs1) : (xs0 || xs1.[i - size xs0 <- x]).
proof. 
  move => [ge0_i]; rewrite size_append => gi_size.  
  case (i < size xs0) => hcase.
    rewrite ge0_i; simplify.
    apply arrayP; split; first by smt.
    by move => k hk; smt.
    simplify.
    apply arrayP; split; first by smt.
    rewrite size_set size_append; move => k hk.
    rewrite get_set; first by rewrite size_append.
    case (k=i) => hc; subst.
      rewrite get_append; first by rewrite size_append size_set. 
      cut ->: 0 <= i < size xs0 <=> false by smt. simplify.
      rewrite get_set; first by smt.
      by trivial.
      by smt.
qed.

lemma nosmt set_append_left (xs0 xs1:'x array) (i:int) v:
 0 <= i < size xs0 =>
 (xs0 || xs1).[i <- v] = (xs0.[i <- v] || xs1)
by [].

lemma nosmt set_append_right (xs0 xs1:'x array) (i:int) v:
 size xs0 <= i < size xs0 + size xs1 =>
 (xs0 || xs1).[i <- v] = (xs0 || xs1.[i - size xs0 <- v])
by [].

lemma make_append (a:'a) (l1 l2:int):
  0 <= l1 => 0 <= l2 => offun (fun k, a) (l1 + l2) = (offun (fun k, a) l1 || offun (fun k, a) l2).
proof.
  move=> le0_l1 le0_l2.
  apply arrayP; split; first by rewrite size_append ?size_offun // => /#. 
  move => i Hisize.
  rewrite get_append; first by smt.
  case (0 <= i < size (offun (fun (_ : int) => a) l1)) => hc. 
    rewrite ?offunifE.
    cut ->: 0 <= i < l1 + l2 <=> true by smt.
    by cut ->: 0 <= i < l1 <=> true by smt.
    rewrite ?offunifE.
    cut ->: 0 <= i < l1 + l2 <=> true by smt.
    cut ->: 0 <= i - size (offun (fun (_ : int) => a) l1) < l2 <=> true.
      simplify; split; first by smt.
      move => hi.      
      rewrite size_offun max_ler => //.
      move : Hisize; rewrite size_offun max_ler; first by smt.
      by smt.
    by simplify.
qed.

(** mapi *)
op mapi: (int -> 'x -> 'y) -> 'x array -> 'y array.

axiom size_mapi (f:int -> 'x -> 'y) (xs:'x array):
  size (mapi f xs) = size xs.

axiom get_mapi (f:int -> 'x -> 'y) (xs:'x array) (i:int):
  0 <= i < size xs =>
  (mapi f xs).[i] = f i (xs.[i]).

lemma mapi_mapi (f:int -> 'x -> 'y) (g:int -> 'y -> 'z) xs:
 mapi g (mapi f xs) = mapi (fun k x, g k (f k x)) xs.
proof.
  apply arrayP; split.
    by rewrite !size_mapi.
    by move=> i; rewrite !size_mapi=> i_bnd; rewrite ?get_mapi ?size_mapi.
qed.

lemma mapi_id (f:int -> 'x -> 'x) (xs:'x array):
 (forall k x, 0 <= k < size xs => f k x = x) =>
 mapi f xs = xs.
proof.
  move=> f_id; apply arrayP; split.
    by rewrite size_mapi.
    by move=> i; rewrite !size_mapi=> i_bnd; rewrite ?get_mapi ?length_mapi ?f_id.
qed.

(** take *)
op take (l:int) (xs:'a array) = mkarray (take l (ofarray xs)) axiomatized by takeE.

lemma size_take (xs:'a array) (l:int):
  0 <= l <= size xs =>
  size (take l xs) = l
by rewrite takeE size_mkarray; smt.

lemma get_take (xs:'a array) (l k:int):
  0 <= k < l <= size xs =>
  (take l xs).[k] = xs.[k].
proof.
  move => Hksize.
  by rewrite ?getE takeE ofarrayK; smt.
qed.

(* drop *)
op drop (l:int) (xs:'a array) = mkarray (drop l (ofarray xs)) axiomatized by dropE.

lemma size_drop (xs:'a array) (l:int):
  0 <= l <= size xs =>
  size (drop l xs) = size xs - l.
proof.
  move => [ge0_h gel_size].
  rewrite dropE size_mkarray size_drop; first by exact ge0_h.
  rewrite size_ofarray max_ler; first by smt.
  by reflexivity.
qed.
    
lemma get_drop  (xs:'a array) (l k:int):
  0 <= l => 0 <= k < size xs-l =>
  (drop l xs).[k] = xs.[l + k].
proof.
  move => Hl Hksize.
  by rewrite ?getE dropE ofarrayK; smt.
qed.

lemma take_drop (xs:'a array) (l:int):
  0 <= l <= size xs =>
  (take l xs || drop l xs) = xs.
proof.
  move => Hsize.
  apply arrayP; split; first by smt.    
  move => k Hksize.
  by rewrite get_append; smt. 
qed.

(** all *)
op all (p : 'x -> bool) (xs : 'x array) : bool = all p (ofarray xs) axiomatized by allE.

lemma allP_mem p (xs:'x array):
  all p xs <=> (forall x, mem (ofarray xs) x => p x) by smt.

lemma allP p (xs:'x array):
  all p xs <=>
  (forall i, 0 <= i < size xs => p xs.[i]).
proof. rewrite allP_mem. split. smt. progress. smt timeout=60. qed.

(** cons *)
op (::) (x : 'x) (xs : 'x array) = (mkarray [x]) || xs axiomatized by consE.

lemma size_cons (x:'x) (xs:'x array):
  size (x::xs) = 1 + size xs
by (rewrite consE; smt).
    
lemma get_cons (x:'x) (xs:'x array) (i:int):
  0 <= i <= size xs =>
  (x::xs).[i] = (0 = i) ? x : xs.[i - 1].
proof.
  move => hi; rewrite consE.
  case (xs = empty) => hcase.
    cut ->: (mkarray [x] || xs) = mkarray [x] by apply arrayP; split; smt. 
    move : hi; rewrite hcase size_empty.
    move => [ge0_i gei_0].
    rewrite (lez_anti i 0); first by smt.
    by simplify; rewrite getE ofarrayK; smt.
    case (i <= 0)=> eq0_i.
    rewrite (lez_anti i 0); first by smt.
    simplify; rewrite get_append_left; first by smt.
    by rewrite getE ofarrayK; smt.
    by rewrite get_append_right; smt.
qed.

lemma cons_nonempty (x:'x) (xs:'x array):
  x::xs <> empty.
proof.
  by rewrite -not_def=> cons_empty;
    cut:= congr1 Array.size (x::xs) empty _=> //;
    rewrite size_empty size_cons; smt.
qed.

lemma consI (x y:'x) (xs ys:'x array):
  x::xs = y::ys <=> x = y /\ xs = ys.
proof.
  split; last by move=> [-> ->]. 
  rewrite !arrayP. move => [len val].
  split. 
    cut:= val 0 _; first smt.
    by rewrite 2?get_cons /=; first 2 smt.
    move : len. rewrite 2!size_cons. 
    progress. smt. cut := val (i + 1) _; first smt.
    rewrite 2?get_cons; first 2 smt.
    cut ->: (0 = i + 1) = false by smt.
    cut ->: i + 1 - 1 = i by smt.
    smt.
qed.

(** sub *)
op sub (xs : 'x array) (i : int) (j : int) : 'x array = take j (drop i xs) axiomatized by subE.

lemma size_sub (xs:'x array) (s l:int):
  0 <= s => 0 <= l => s + l <= size xs =>
  size (sub xs s l) = l by
by (rewrite subE; smt).

lemma get_sub (xs:'x array) (s l i:int):
  0 <= s => 0 <= l => s + l <= size xs =>
  0 <= i < l =>
  (sub xs s l).[i] = xs.[i + s]
by (rewrite subE; smt).

lemma sub_complete (xs : 'x array) (l : int):
  l = size xs => 
  sub xs 0 l = xs.
proof. by move => hl; apply arrayP; split; smt. qed. 
    
(** snoc *)
op (:::) (xs : 'x array) (x : 'x) : 'x array = xs || (mkarray [x]) axiomatized by snocE.

lemma size_snoc (x:'x) (xs:'x array):
  size (xs:::x) = size xs + 1
by (rewrite snocE; smt).

lemma get_snoc (xs:'x array) (x:'x) (i:int):
  0 <= i <= size xs =>
  (xs:::x).[i] = (i < size xs) ? xs.[i] : x.
proof.
  move => Hi.
  rewrite snocE.
  case (i < size xs) => hcase.
    rewrite get_append_left; smt; reflexivity.
    rewrite get_append_right; first by smt.
    cut eqi_size : i = size xs by smt.
    by rewrite getE eqi_size ofarrayK; smt.
qed.  

lemma snoc_nonempty (xs:'x array, x:'x):
  xs:::x <> empty.
proof.
  by rewrite -not_def=> snoc_empty;
    cut:= congr1 Array.size (xs:::x) empty _=> //;
    rewrite size_empty size_snoc; smt.
qed.

lemma array_ind_snoc (p:'x array -> bool):
  p empty =>
  (forall x xs, p xs => p (xs:::x)) =>
  (forall xs, p xs).
proof.
  move=> p0 prec xs.
  cut h : (forall n, 0 <= n => forall xs, Array.size xs = n => p xs).
    elim => //; first smt.
    move=> i ipos hrec xs' hlen.
    cut ->: xs' = (sub xs' 0 i):::xs'.[i] by (apply arrayP; smt).
    apply prec.
    apply hrec. 
    by rewrite size_sub; smt.
    by apply (h (size xs) _);smt.
qed.

(** blit *)
op blit (dst : 'x array) (doff : int) (src : 'x array) (soff : int) (l : int) : 'x array = (take doff dst) || (sub src soff l) || (drop (doff + l) dst) axiomatized by blitE.

lemma size_blit (dst src:'x array) (dOff sOff l:int):
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= size dst =>
  sOff + l <= size src =>
  size (blit dst dOff src sOff l) = size dst
by (rewrite blitE; smt).
    
lemma get_blit (dst src:'x array) (dOff sOff l i:int):
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= size dst =>
  sOff + l <= size src =>
  0 <= i < size dst =>
  (blit dst dOff src sOff l).[i] =
    (dOff <= i < dOff + l) ? src.[i - dOff + sOff]
                           : dst.[i].
proof.  
  move => ge0_dOff ge0_sOff ge0_l gedOffl_size gesOffl_size [ge0_i gi_size].
  rewrite blitE.
  case (i < dOff) => hc.
    cut ->: dOff <= i < dOff + l <=> false by smt.
    by simplify; smt. 
  case (i < dOff + l) => hc2; last by smt.
  cut ->: (if dOff <= i && true then src.[i - dOff + sOff] else dst.[i]) = src.[i - dOff + sOff] by smt.
  rewrite get_append_right; first by smt.
  rewrite size_take; first by smt.
  rewrite get_append_left; expect 2 by smt. 
qed.

(** equalities *)
lemma list_array_eq (l : 'a list) (a : 'a array) :
    a = mkarray l <=>
    (size l = size a
    /\ (forall i, 0 <= i < size a => nth witness l i = a.[i])).
proof.   
  rewrite arrayP size_mkarray. 
  cut ->: (forall (i : int), 0 <= i < size a => a.[i] = (mkarray l).[i]) = (forall (i : int), 0 <= i < size a => a.[i] = nth witness (ofarray (mkarray l)) i) by smt.
  by rewrite ofarrayK; smt. 
qed. 

lemma mkarray_ofarray_eq (x : 'a list) (xs : 'a array): (mkarray x = xs) = (x = ofarray xs).
proof. 
  case (size x <> size xs) => hc; first by smt.
  cut h_size : size x = size xs by smt.
  case (forall i, 0 <= i < size xs => xs.[i] = nth witness x i) => hc'; last by smt.
  rewrite arrayP => //.
  cut ->: size (mkarray x) = size xs <=> true by smt.
  cut ->: (forall (i : int), 0 <= i < size (mkarray x) => (mkarray x).[i] = xs.[i]) = (forall (i : int), 0 <= i < size xs => xs.[i] = nth witness x i) by smt. 
  cut ->: (forall (i : int), 0 <= i < size xs => xs.[i] = nth witness x i) = true by smt.
  rewrite (eq_from_nth witness x (ofarray xs)); first 2 by smt.
  by trivial.
qed.

lemma drop_empty (x : int) (xs : 'a array) : xs = empty => drop x xs = empty.
proof.
  move => ->. rewrite dropE. rewrite emptyE. rewrite ofarrayK. smt.
qed.    

lemma array_ind_struct (xs : 'a array) :
  0 < size xs =>
  xs = xs.[0] :: drop 1 xs.
proof.
  move => l0_size.
  apply arrayP; smt.
qed.
    
theory Darray.

  import MUnit.
  require DProd.
  
  op darray (d: 'a distr) (n : int) = dapply (fun x, mkarray x) (dlist d n) axiomatized by darrayE.

  lemma mu_darray_dlist (d : 'a distr) n xs:
    mu (darray d n) (pred1 xs) = mu (dlist d n) (pred1 (ofarray xs)).
  proof. 
    rewrite /pred1. rewrite darrayE. simplify. rewrite mux_dmap. congr. rewrite fun_ext. rewrite /(==). move => x. rewrite /pred1. by smt.
  qed.

  lemma mux_darray_dlist (d : 'a distr) n xs:
    mu_x (darray d n) xs = mu_x (dlist d n) (ofarray xs).
  proof. by smt. qed.

  lemma darray_support (d : 'a distr) n xs :
    support (darray d n) xs <=> support (dlist d n) (ofarray xs).
  proof. by smt. qed.
      
  lemma darray_support0 (d : 'a distr) n xs:
    n <= 0 =>
    support (darray d n) xs <=> xs = empty.
  proof.
     cut darray0 : n <= 0 => darray d n = dunit empty. 
      move => len_0. 
      rewrite darrayE dlistE Int.foldle0; first by exact len_0.
      rewrite -pw_eq /(==) => x.
      by rewrite mux_dmap; rewrite /pred1; smt. 
    by smt.
  qed.
  
  lemma darray_support_ge0 (d : 'a distr) n xs:
    0 <= n =>
    support (darray d n) xs <=> size xs = n /\ all (support d) xs.
  proof. 
    move=> le0_n.
    rewrite darrayE support_dmap.
    simplify; progress; first by smt.
      by rewrite allE ofarrayK; smt.
      by exists (ofarray xs); rewrite mkarrayK; smt.
  qed.
  
  clone import Bigop as Prod with
  type t <- real,
  op   Support.idm <- 1%r,
  op   Support.(+) <- Real.( * )
  proof * by smt.

  lemma mux_darray (d : 'a distr) n xs:
    0 <= n =>
    mu (darray d n) (pred1 xs)
      = if   n = size xs
      then big predT (fun x => mu d (pred1 x)) (ofarray xs)
      else 0%r.
  proof. 
    move=> le0_n. rewrite mux_darray_dlist. 
    rewrite mux_dlist. exact le0_n.
    rewrite size_ofarray. reflexivity.
  qed.

  lemma mux_darray_eq (d : 'a distr) s1 s2:
    s1 = s2 =>
    mu (darray d (Array.size s1)) (pred1 s1) = mu (darray d (size s2)) (pred1 s2)
  by (rewrite !mux_darray //= 1,2:smt).

  (**OLD LEMMAS*)
  lemma mu_neg (len:int) (d:'a distr) (p:'a array -> bool):
    len < 0 =>
    mu (darray d len) p = charfun p empty.
  proof. 
    move => llen_0.
    cut darray0 : len <= 0 => darray d len = dunit empty. 
      move => len_0. 
      rewrite darrayE dlistE Int.foldle0; first by exact len_0.
      rewrite -pw_eq /(==) => x.
      by rewrite mux_dmap; rewrite /pred1; smt. 
    by smt.
  qed.
      
  lemma mu_x_neg (len:int) (d:'a distr) (x:'a array):
    len < 0 =>
    mu_x (darray d len) x = if x = empty then 1%r else 0%r.
  proof.
    move => hlen.
    rewrite mu_neg; first by done.
    by smt.
  qed.

  lemma supp_neg (len:int) (d:'a distr) (x:'a array):
    len < 0 =>
    in_supp x (darray d len) <=> x = empty
  by [].

  lemma weight_neg (len:int) (d:'a distr):
    len < 0 =>
    weight (darray d len) = 1%r
  by [].

  (* Non-negative length case *)
  lemma mu_x_def (len: int) (d:'a distr) (x:'a array):
    len = size x =>
    mu_x (darray d len) x = foldr (fun x p, p * mu_x d x) 1%r (ofarray x).
  proof. 
    move => eqlen_size.
    rewrite mux_darray. smt. cut ->: len = size x <=> true by smt.
    simplify. rewrite /big. rewrite foldr_map. simplify. rewrite filter_predT. rewrite /mu_x.
    congr. cut ->: (fun (x0 : 'a) (p : real) => p * mu d (pred1 x0)) = fun (x0 : 'a) (p : real) => mu d (pred1 x0) * p. apply fun_ext. rewrite /(==). move => x0. cut ->: (fun (p : real) => mu d (pred1 x0) * p) = (fun (p : real) => p * mu d (pred1 x0)). apply fun_ext. rewrite /(==). smt. reflexivity. reflexivity.
  qed.

  lemma supp_def (len:int) (x:'a array) (d:'a distr):
    0 <= len =>
    in_supp x (darray d len) <=>
    (size x = len /\ all (support d) x) by [].

  lemma supp_full (len:int) (d:'a distr) (x:'a array):
    0 <= len =>
    (forall y, in_supp y d) =>
    size x = len <=> in_supp x (darray d len). 
  proof.
    move => hlen y; split.
      move => hsize.
      rewrite supp_def //.
      split; first by done.
      by smt.
      move => hsupp.
      by smt.
  qed.
    
  lemma supp_len (len:int) (x: 'a array) (d:'a distr):
    0 <= len =>
    in_supp x (darray d len) => size x = len by [].

  lemma supp_k (len:int) (x: 'a array) (d:'a distr) (k:int):
    0 <= k < len =>
    in_supp x (darray d len) =>
    in_supp x.[k] d. 
  proof.
    move => hk.
    rewrite supp_def; first by smt.
    by move => [hsize] => hall; smt.
  qed.
  
  (* This would be a lemma by definition of ^
     if we had it in the correct form (if we know that Real is a field) *)
  lemma weight_darray_dlist (d : 'a distr) len: weight (darray d len) = weight (dlist d len).
  proof. smt. qed.

  lemma darray_ll (d : 'a distr) n: is_lossless (darray d n) <=> is_lossless (dlist d n).
  proof. smt. qed.
  
  lemma darrayL (d:'a distr) len:
    0 <= len =>
    weight d = 1%r =>
    weight (darray d len) = 1%r.
  proof. 
    move => le0_len.
    cut ->: weight d = 1%r <=> is_lossless d by smt.
    cut ->: weight (darray d len) = 1%r <=> is_lossless (darray d len) by smt.
    smt.
  qed.

   (* if len is negative, then uniformity is easy to prove.
     otherwise, the folded function can be replaced with the same constant for x and y
     (but we need to know that it is only applied to elements of d's support,
      which justifies leaving it as an axiom for now) *)
  axiom darray_uniform (d:'a distr) len:
    is_uniform d =>
    is_uniform (darray d len).
end Darray.

import Darray.

lemma mkarray_map (xs : 'a list) (f : 'a -> 'b) : mkarray (map f xs) = map f (mkarray xs).
proof. by rewrite /map ofarrayK; reflexivity. qed.

(** 
  The probability of sampling the array (x::xs) is the 
  probability of sampling xs times the probability of 
  sampling x.
*)
lemma mu_x_cons (x:'a) (xs:'a array) (d:'a distr): forall len,
 len = size xs =>
 mu_x (Darray.darray d (1+len)) (x::xs)
 = (mu_x d x) * (mu_x (Darray.darray d len) xs). 
proof.
  progress.
  rewrite consE.
  rewrite mux_darray_dlist.
  rewrite mux_darray_dlist.
  rewrite mux_dlist. smt.
  cut ->: size (ofarray (mkarray [x] || xs)) = 1 + size xs.
    rewrite size_ofarray. rewrite size_append. rewrite size_mkarray. simplify. trivial.
  simplify.
  rewrite mux_dlist. smt.
  cut ->: size (ofarray xs) = size xs by rewrite size_ofarray.
  simplify. smt.
qed.

require import DProd.

(**
  The probability distribution of an array of size 'len+1' is the 
  product between the probability distribution of the elements of
  the array and the probability distribution of an array of size
  'len'.
*)
axiom darray_cons (d:'a distr) (len:int):
 0 <= len =>
 Darray.darray d (1+len) = dapply (fun x,fst x::snd x) (d `*` (Darray.darray d len)).
    
(**
  The probability of sampling an array of type (xs || ys) is the
  product between the probability of sampling xs and the probability
  of sampling ys.
*)
lemma mu_x_app (x:'a) (xs ys:'a array) (d:'a distr): forall lxs lys,
 lxs = size xs =>
 lys = size ys =>
 mu_x (darray d (lxs+lys)) (xs || ys) 
 = (mu_x (darray d lxs) xs) * (mu_x (darray d lys) ys).
proof.
  progress.
  rewrite ?mux_darray_dlist.
  rewrite mux_dlist. smt.
  cut ->: size (ofarray (xs || ys)) = size xs + size ys by smt.
  simplify.
  rewrite mux_dlist. smt.
  cut ->: size (ofarray xs) = size xs by smt.
  simplify.
  rewrite mux_dlist. smt.
  cut ->: size (ofarray ys) = size ys by smt.
  simplify.
  smt.
qed.

(**
   Sampling an array with size len is equivalent to sampling a bigger array 
   and then cutting him to size len.
*)
theory DArrayTake.
 type t.
 module M = {
  proc gen1(len:int, d: t distr) : t array = {
    var xs: t array;
    xs = $darray d len;
    return xs;
  }
  proc gen2(len' len:int, d: t distr) : t array = {
    var xs: t array;
    xs = $darray d len';
    xs = take len xs;
    return xs;
  }
 }.

 axiom darray_take_equiv:
  equiv [ M.gen1 ~ M.gen2 : 
         ={len, d} /\ 0 <= len{2} <= len'{2} ==> ={res} ].
end DArrayTake.

(**
  Sampling values individually and then assigning them to
  array positions is equivalent to sampling the entire array at one time.
*)
theory DArrayWhile.
 type t.
 module M = {
  proc gen1(len:int, d: t distr, dflt: t) : t array = {
    var i: int;
    var x: t;
    var xs: t array;
    i = 0;
    xs = offun (fun k, dflt) len;
    while (i < len) {
      x = $d;
      xs.[i] = x;
      i = i+1;
    }
    return xs;
  }
  proc gen2(len:int, d: t distr) : t array = {
    var xs: t array;
    xs = $darray d len;
    return xs;
  }
 }.

 axiom darray_loop_equiv:
  equiv [ M.gen1 ~ M.gen2 : 
         ={len, d} /\ 0 <= len{1} ==> ={res} ].
end DArrayWhile.

(**
  Sampling two values and then assigning to an array the output
  of a function that takes them as input is equivalent to generating two
  arrays and then map the function between the two arrays.
*)
theory DArrayWhile2.
 type t1, t2, t.
 module M = {
  proc gen1(len:int,d1:t1 distr,d2:t2 distr,f:t1->t2->t,dflt:t) : t array = {
    var i: int;
    var x: t1;
    var y: t2;
    var z: t array;
    i = 0;
    z = offun (fun k, dflt) len;
    while (i < len) {
      x = $d1;
      y = $d2;
      z.[i] = f x y;
      i = i+1;
    }
    return z;
  }
  proc gen2(len:int,d1:t1 distr,d2:t2 distr,f:t1->t2->t) : t array = {
    var x: t1 array;
    var y: t2 array;
    var z: t array;
    x = $darray d1 len;
    y = $darray d2 len;
    z = offun (fun k, f x.[k] y.[k]) len;
    return z;
  }
 }.

 axiom darray2_loop_equiv:
  equiv [ M.gen1 ~ M.gen2 : 
         ={len, d1, d2, f} /\ 0 <= len{1} ==> ={res} ].

end DArrayWhile2.
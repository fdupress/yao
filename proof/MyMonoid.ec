require import Monoid.
require import Fun.
require import Distr.
require import FSet.

lemma cpOrDcpAnd : forall (P Q R:'a cpred), cpAnd (cpOr P Q) R = cpOr (cpAnd P R) (cpAnd Q R)
  by (intros _ _ _;rewrite /cpOr /cpAnd;apply fun_ext=> x /=;apply orDand).

lemma cpAndC : forall (P Q:'a cpred), cpAnd P Q = cpAnd Q P
  by (intros _ _;rewrite /cpAnd;apply fun_ext=> x /=;apply andC).

lemma cpOrs_empty: cpOrs empty<:'a cpred> = cpFalse
  by (apply fun_ext=> x;rewrite /cpOrs /cpFalse Mbor.sum_empty /Mbor.Base.Z /Bbor.Z //).

lemma cpOrs_add : forall (X:('a cpred) set) (P:'a cpred), ! mem P X => cpOrs (add P X) = cpOr P (cpOrs X)
  by (intros=> _ _ _;apply fun_ext=> x;rewrite /cpOrs /cpOr Mbor.sum_add /Mbor.Base.(+) /Bbor.(+) //).

lemma nosmt rw_fun_ext : forall (f g : 'a -> 'b), f = g <=> f == g
  by (intros f g;apply iffI;[intros -> // |apply fun_ext]).
(*
lemma andS : forall (a b c:bool), (a /\ b) = (a /\ c) <=> b = c.
intros a b c.
apply iffI.
case a.
smt.
simplify.
smt.
intros -> //.
split.
split.
smt.
trivial.

lemma cpAndS : forall (P Q R:'a cpred), (cpAnd P Q) = (cpAnd P R) <=> Q = R.
  intros P Q R.
  apply iffI.
  rewrite ! rw_fun_ext /cpAnd=> h x.
  cut := h x=> /=.
  
  smt.
  intros h.
  apply fun_ext=> x.
  generalize h.

  intros -> //.
  delta cpAnd.
  intros P Q R.
  apply iffI.

  delta cpAnd.
*)

lemma cpOrK : forall (P:'a cpred), cpOr P P = P.
intros _.
rewrite /cpOr.
apply fun_ext=> _ /=.
apply orK.
qed.

lemma cpOrC : forall (P Q:'a cpred), (cpOr P Q) = (cpOr Q P).
intros _ _.
delta cpOr.
apply fun_ext=> _ /=.
apply orC.
qed.

lemma cpOrA : forall (P Q R:'a cpred), cpOr (cpOr P Q) R = cpOr P (cpOr Q R).
intros _ _ _.
delta cpOr.
apply fun_ext=> _ /=.
apply orA.
qed.

lemma add_add : forall (x:'a) y X, add x (add y X) = add y (add x X).
intros x y X.
apply set_ext=> a.
rewrite ! mem_add orA (orC (a = y)) -orA //.
qed.

lemma cpOrsInv : forall (Q:'a cpred) s, mem Q s =>
cpOrs (add Q s) = cpOrs s.
intros Q s.
elim/set_ind s.
smt.
intros P X hnm hr h.
case (P=Q)=> heq;
  first by rewrite heq -add_in_id ? mem_add //.
rewrite add_add.
rewrite cpOrs_add.
rewrite mem_add nor //.
generalize heq h.
rewrite mem_add.
rewrite -rw_neqF (rw_eq_sym P)=> -> /= h.
rewrite hr //.
rewrite cpOrs_add //.
qed.


lemma img_add : forall (f:'a -> 'b) (X:'a set) (x:'a), !mem x X=> img f (add x X) = add (f x) (img f X).
intros f X x hnm.
apply set_ext=> y.
rewrite img_def mem_add img_def.
apply iffI.
  by intros [z [h1]];rewrite mem_add;case (z = x)=> h2 /=;[
       subst;right=> // |
       intros h3;left;exists z=> //].
  by case (y = f x)=> /= h1;[
       exists x;rewrite mem_add;split;[apply eq_sym=> // |right=> //] |
       intros [z [h2 h3]];exists z;rewrite mem_add;split=> //;left=> //].
qed.

lemma distrOrs : forall (X:('a cpred) set) (P:'a cpred),
  cpAnd (cpOrs X) P = cpOrs (img (cpAnd P) X).
proof strict.
intros X P.
elim/set_ind X;
  first by rewrite img_empty cpOrs_empty //.
intros P' s hm hr.
rewrite img_add //.
case (mem (cpAnd P P') (img (cpAnd P) s))=> h;
  last by rewrite ! cpOrs_add // cpOrDcpAnd cpAndC hr //.
rewrite (cpOrsInv (cpAnd P P')) //.
generalize h.
rewrite img_def.
intros=> [Q [val mem]].
rewrite cpOrs_add // cpOrDcpAnd -(add_rm_in Q) //.
rewrite cpOrs_add;
  first by rewrite mem_rm -rw_nand nnot;right. 
rewrite cpOrDcpAnd -cpOrA (cpAndC P') (cpAndC Q) -val cpOrK -(cpAndC Q) -cpOrDcpAnd.
rewrite -cpOrs_add;
  first by rewrite mem_rm -rw_nand nnot;right. 
by rewrite add_rm_in //.
qed.

require import FSet.
require import Real.
require import Distr.

require import Monoid.

theory Mean.
  type base.

  op d : base distr.
  
  module type Worker = {
    fun work(x:base) : bool
  }.

  module Rand(W:Worker) = {
    var x : base
    fun randAndWork() : bool = {
      var r : bool;
      x = $d;
      r = W.work(x);
      return r;
    }
  }.

require import ISet.
require import Pair.

  lemma prCond: forall (A<:Worker{Rand}) &m (v:base),
      Pr[Rand(A).randAndWork() @ &m : (cpAnd (lambda x, fst x) (lambda x, v = (snd x))) (res, Rand.x)] = (mu_x d v) * Pr[A.work(v) @ &m : res].
  proof strict.
  intros A &m v.
  cut hPr : forall &hm, Rand.x{hm} = v => Pr[A.work(v) @ &hm : Rand.x = v /\ res] =
    Pr[A.work(v) @ &hm : res].
    intros &hm h;
    cut -> : Pr[A.work(v) @ &hm : Rand.x = v /\ res] = Pr[A.work(v) @ &hm : Rand.x = v] + Pr[A.work(v) @ &hm : res] - Pr[A.work(v) @ &hm : Rand.x = v \/  res]
      by (rewrite Pr mu_or;smt);
    cut -> : (Pr[A.work(v) @ &hm : Rand.x = v] = Pr[A.work(v) @ &hm : Rand.x = v \/ res])
      by (equiv_deno (_ : ={glob A,Rand.x, x} /\ Rand.x{1}=v ==> ={Rand.x} /\ Rand.x{1}=v)=> //;fun (={Rand.x} /\ Rand.x{1} = v)=> //);
    smt.
  bdhoare_deno (_:true ==> (cpAnd (lambda x, fst x) (lambda x, v = (snd x))) (res, Rand.x))=> //;
    last by intros &h;split;intros h;apply h.
  fun.
  seq 1 : (v = Rand.x) (mu_x d v) Pr[A.work(v) @ &m : res] 1%r 0%r true.
    by trivial.
    by (rnd;skip;progress;delta mu_x;smt).
    simplify cpAnd fst snd.
    admit. (*by pr*)
    by hoare;call (_:! v = Rand.x ==> !v = Rand.x)=> //;[
        fun (!v = Rand.x)=> //;skip;progress;assumption|
        skip;progress;try (rewrite -rw_nand;right);smt].
    by trivial.
  qed.

  lemma introOrs : 
    forall &m, forall (W<:Worker{Rand}) (q:(bool*base) -> bool), Finite.finite (support d) =>
      q = cpAnd (cpOrs (img (lambda x, lambda y, x = snd y) (Finite.toFSet (support d))))  (lambda x, fst x) =>
      Pr[Rand(W).randAndWork() @ &m : res] = Pr[Rand(W).randAndWork() @ &m : q (res, Rand.x)].
  intros &m W q finite qVal.
  equiv_deno (_: ={glob W} ==> ={res} /\ in_supp Rand.x{2} d)=> //.
    fun.
    call (_: ={glob W, x} ==> ={res})=> //;first by fun true => //.
    rnd=> //.
  subst.
  rewrite /fst /snd.
  progress assumption.
  rewrite /cpOrs or_exists.
  exists (lambda (y : (bool * base)), Rand.x{2} = snd y).
  split=> //.
  rewrite img_def;
  exists Rand.x{2}=> /=;
  cut : mem Rand.x{2} ((Finite.toFSet (support d)))
    by rewrite Finite.mem_toFSet // /support mem_create //
  => -> /=; apply fun_ext=> x //.
  smt.
  qed.

pred inj (b:'a FSet.set) (f:'a -> 'b) = forall x y, mem x b=> mem y b => f x = f y=> x = y.

lemma bij (b:'a FSet.set) (f:'a -> 'b) :
  inj b f =>
  exists (f':'b -> 'a),
    (forall (x:'a), mem x b => f' (f x) = x) /\
    (forall (x:'b), mem x (img f b) => f (f' x) = x).
intros h.
case (exists x, mem x b).
intros=> [o ho].
pose p := lambda y, (lambda x, f x = y).
pose f' := (lambda (y:'b), if mem y (img f b) then pick (filter (p y) b) else o).
exists f'.
split;intros x hmem;simplify f'.
  by (case (mem (f x) (img f b));last by rewrite mem_img //);
     cut rw : filter (p (f x)) b = FSet.single x by (
       apply FSet.set_ext=> z /=;
       rewrite FSet.mem_filter FSet.mem_single;delta p=> /=;
       apply iffI=> //;intros=> [mem feq];apply h=> //
     );rewrite rw FSet.pick_single //.
  rewrite hmem /=.
  generalize hmem.
  rewrite img_def=> [z [eqz memz]].
  change (p x (pick (filter (p x) b))).
cut := FSet.mem_pick (filter (p x) b) _;first by
rewrite -empty_nmem;
  pose q := lambda x0, ! mem x0 (filter (p x) b);
  change (!forall x0, q x0);
  apply (nforall q);
  delta q=> /=;
exists z;rewrite FSet.mem_filter //.
by rewrite FSet.mem_filter //.
smt.
save.

  lemma Mean :
    forall &m, forall (W<:Worker), Finite.finite (support d) =>
        Pr[Rand(W).randAndWork()@ &m:res] =
          Mrplus.sum (lambda (x:base), (mu_x d x)*Pr[W.work(x)@ &m:res]) (Finite.toFSet (support d)).
  proof strict.
  intros &m W fin.
  pose bs := Finite.toFSet (support d).
  pose s := img (cpAnd (lambda x, fst x)) (img (lambda x, lambda y, x = snd y) bs).
  rewrite(introOrs &m W (cpOrs s)) //;first by rewrite /s /bs rw_eq_sym;apply distrOrs.
  cut -> : Pr[Rand(W).randAndWork() @ &m : (cpOrs s) (res, Rand.x)] =
    Mrplus.sum (lambda (p:(bool*base) cpred), Pr[Rand(W).randAndWork() @ &m : p (res, Rand.x)]) s
    by admit. (*rewrite Pr*)
  pose f  := lambda (x:base), cpAnd (lambda y, fst y) (lambda y, x = snd y).

  cut f_inj : inj bs f by (
    intros x y hm1 hm2 h;
    cut : (f x) (true, y) = (f y) (true, y) by smt;
    simplify f cpAnd fst snd=> -> //).

  cut := bij bs f _=> //.
  intros=> [f' [bij1 ]].

  cut eqS : s = img f bs by (
    rewrite /s;
    apply FSet.set_ext=> x;
    rewrite ! img_def;
    delta f=> /=;
    by apply iffI;[
      intros [y [h1 ]];rewrite img_def=> [ y' [h3 h4]];
      exists y';split=> //;subst=> // |
      intros [y [h1 h2]];
      exists (lambda (y0 : (bool * base)), y = snd y0);
      split=> //;rewrite img_def /=;exists y;rewrite h2 //]
  ).
  rewrite -eqS=> bij2.
  cut eqS2 : bs = img f' s.
    rewrite eqS.
    apply FSet.set_ext=> x /=.
    apply iffI;
      first by intros h;rewrite -bij1 // ! mem_img //.
      rewrite img_def=> [p [h1]].
      rewrite img_def=> [y [h2 h3]].
      subst;rewrite bij1 //.
  rewrite rw_eq_sym (Mrplus.sum_chind _ f' f) //.
  congr.
  apply fun_ext=> x /=.
  delta f=> /=.
  rewrite (prCond W &m x) //.
  qed.

end Mean.
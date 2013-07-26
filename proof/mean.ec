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

  lemma test: forall (A<:Worker{Rand}) &m (v:base) prWork,
    bd_hoare[A.work : x = v ==> res] = prWork =>
      Pr[Rand(A).randAndWork() @ &m : res /\ Rand.x = v] = (mu_x d v) * prWork.
  proof strict.
  intros A &m v prWork lWork.
  bdhoare_deno (_:true ==> res /\ Rand.x = v)=> //.
  fun.
  seq 1 : (Rand.x = v) (mu_x d v) prWork 1%r 0%r true.
    by trivial.
    by (rnd;skip;progress;delta mu_x;smt).
    by call lWork.
    by hoare;call (_:! Rand.x = v ==> !Rand.x = v)=> //;[
        fun (!Rand.x = v)=> //;skip;progress;assumption|
        skip;progress;try (rewrite -rw_nand;right);assumption].
    by trivial.
  qed.

require import ISet.

  lemma Mean :
    forall &m, forall (W<:Worker), Finite.finite (support d) =>
        Pr[Rand(W).randAndWork()@ &m:res] =
          Mrplus.sum (lambda (x:base), (mu_x d x)*Pr[W.work(x)@ &m:res]) (Finite.toFSet (support d)).
    intros &m W fin.
    
  
end Mean.

type input.
type random.
type output.

module M = {
  fun s(i:input, d:input -> output distr) : output = {
    var o : output;
    o = $ (d i);
    return o;
  }
}.

type t.
module type T = { fun preInit() : t fun work(i:t) : bool}.

module G(A:T) = {
  var i : t
  fun f() : bool = {
    var b : bool;
    i = A.preInit();
    b = A.work(i);
    return b;
  }
}.

lemma test: forall (A<:T{G}) &m (v:t) x y,
  islossless A.preInit =>
  islossless A.work =>
  bd_hoare[A.preInit : true ==> res = v] = x =>
  bd_hoare[A.work : G.i = v ==> res] = y =>
  Pr[G(A).f() @ &m : res /\ G.i = v] = x * y.
intros A &m v x y losslessPreInit losslessWork lx ly.
bdhoare_deno (_:true ==> res /\ G.i = v)=> //.
fun.
seq 1 : (G.i = v) x y (Pr[A.preInit() @ &m : true]-Pr[A.preInit() @ &m : res = v]) 0%r true.
by trivial.
by call lx.
by call ly.
by hoare;call (_:! G.i = v ==> !G.i = v)=> //;[
     fun (!G.i = v)=> //;skip;progress;assumption|
     skip;progress;try (rewrite -rw_nand;right);assumption].
by trivial.
qed.

progress.
op r : real.
op p' : input -> bool.

op x : input.

op a : real.
op b : real.
op c : real.

lemma test: forall (A<:T) &m (p:output->bool) di d,
  ISet.Finite.finite (ISet.support di) => ! di = Dempty.dempty =>
    Pr[G.s(di, d) @ &m : p res] = mu di p'.
intros A &m p adi ad finite nempty.
  bdhoare_deno (_:di=adi/\d=ad ==> p res)=> //.
  fun.
  wp.
  rnd (p' i) (mu di (lambda x, p' x)) (mu (d i) p) a b p.
  by admit.
  by rnd.
  by trivial.
  rnd. skip.
  progress.
  admit.
  admit.

  progress.
  progress.

  progress.
  congr.
  congr=> //.
  trivial.
  simplify.
  rnd.
  simplify.
  skip.
  simplify.
  progress.

lemma test: forall (A<:T) &m (p:output->bool) di d f,
  ISet.Finite.finite (ISet.support di) => ! di = Dempty.dempty =>
    Pr[G.s(di, d, f) @ &m : p res] = Mrplus.sum (lambda x, (mu_x di x) * Pr[G.s((Dunit.dunit x), d, f) @ &m : p res]) (ISet.Finite.toFSet (ISet.support di)).


type r.
type o.

module type T = { fun f(random:r):o }.

module S = {
  fun sample(d:r distr) : r = {
    var random : r;
    random = $d;
    return random;
  }
}.

module M(A:T) = {
  fun f(d:r distr) : o = {
    var random : r;
    var output : o;
    random = S.sample(d);
    output = A.f(random);
    return output;
  }
}.

module 

axiom ax : forall (A<:T) &m, exists (f:r->o), forall (x:r),
  Pr[A.f(x) @ &m : res = f x] = Pr[A.f(x) @ &m : true].

lemma ax2 : forall &m (p:r->bool) d, Pr[S.sample(d) @ &m : p res] = (mu d p).
  intros &m p dd.
  bdhoare_deno (_:d=dd ==> p res)=> //.
  fun.
  rnd.
  skip.
  progress.
  rewrite (_:(lambda (x : r), p x) = p) //.
  apply fun_ext=> x //.
qed.

lemma lem : forall (A<:T) &m (p:o -> bool) d, (forall x, in_supp x d => Pr[A.f(x) @ &m : true] = 1%r) => exists (f:r->o),
  Pr[M(A).f(d) @ &m : p res] = Pr[S.sample(d) @ &m : p (f res)].
  intros A &m p h.
  cut := ax A &m. intros=>[f fv].
  exists f.
  equiv_deno (_: true ==> res{1} = f res{2})=> //.
  fun.
  seq 1 1 : (={random}/\ in_supp random{1} d).
    by inline S.sample;wp;rnd;trivial.
  exists *random{1}.
  elim*.
  intros x.
  call{1} (_: random = x ==> res = f x);[admit|trivial].
qed.

lemma lem2 : forall (A<:T) &m (p:o->bool), (forall x, in_supp x d => Pr[A.f(x) @ &m : true] = 1%r) => exists (f:r->o), Pr[M(A).f() @ &m : p res] =
  mu d (lambda x, p (f x)).
  intros A &m p lossless.
  cut := lem A &m p _. assumption. intros=>[f h].
  exists f.
  rewrite h.
  pose q := (lambda x, p (f x)).
  rewrite (_:Pr[S.sample() @ &m : p (f res)] = Pr[S.sample() @ &m : q res])=> //.
  rewrite (ax2 &m q) //.
qed.

lemma test: forall (A<:T) &m (p:o->bool),  (forall x, in_supp x d => Pr[A.f(x) @ &m : true] = 1%r) => ISet.Finite.finite (ISet.support d) => ! d = Dempty.dempty =>
  Pr[M(A).f() @ &m : p res] = Mrplus.sum (lambda x, (mu_x d x) * Pr[A.f(x) @ &m : p res]) (ISet.Finite.toFSet (ISet.support d)).
  intros A &m p lossless h nempt.
  cut := lem2 A &m p _. assumption. intros=>[f fv].
  rewrite fv.  
  rewrite mean //.
  congr=> //.  
  apply fun_ext=> x /=.
  congr=> //.



assumption.
  
  rewrite rw.

  rewrite Pr lem.
require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Real.
require import Int.
require import Bool.
require import Distr.
require import Fun.
require import Logic.

require import Dkc.
require import MyTools.
require import Garble.
require import GarbleTools.
require AdvGarble.
require import Mean.

lemma prReal :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1 &2,
      (glob ADV){1} = (glob ADV){2} /\
      (Dkc.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=0) =>
    Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work() @ &1 : res] =
      Pr[Garble.Game(Garble.PrvInd(RandGarble), ADV).main() @ &2 : res]
proof.
  admit.
save.

lemma prHybrid :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1 &2,
      (glob ADV){1} = (glob ADV){2} =>
      (Dkc.Dkc.b{1}) /\ (!Dkc.Dkc.b{2}) =>
      (AdvGarble.Adv.l{2}=AdvGarble.Adv.l{1}+1) =>
    Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work() @ &1 : res] =
      Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work() @ &2 : res]
proof.
  admit.
save.

lemma fakePr :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1,
      (Dkc.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=borne) =>
        Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work()@ &1 : res] = 1%r / 2%r
proof.
  admit.
save.

clone Mean as MeanBool with
  type base = bool,
  op d = Dbool.dbool,
  op support = Set.add false (Set.add true Set.empty).
clone Mean as MeanInt with
  type base = int,
  op d = Dinter.dinter 0 (borne).

module AdvWork(Adv:Garble.Adv) : MeanInt.Worker = {
  module Game = Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))
  fun work(x:int) : bool = {
    var r : bool;
    AdvGarble.Adv.l = x;
    r := Game.work();
    return r;
  }
}.

module DkcWork(Adv:Dkc.Adv) : MeanBool.Worker = {
  module Game = Dkc.Game(Dkc.Dkc, Adv)
  fun work(x:bool) : bool = {
    var r : bool;
    Dkc.Dkc.b = x;
    Adv.preInit();
    r := Game.work();
    return r;
  }
}.

module DkcWorkAdv(Adv:Dkc.Adv) = {
  module Game = Dkc.Game(Dkc.Dkc, Adv)
  fun work() : bool = {
    var r : bool;
    Adv.preInit();
    r := Game.work();
    return r;
  }
}.
(*
  axiom Rand :
    forall &m,
      forall (W<:Worker),
        Pr[RandBit(W).randAndWork()@ &m:res] = fold_right
          (lambda (x:base, sum:real), sum + (mu_x d x)*Pr[W.work(x)@ &m:res])
          (0%r)
          (support d).
*)

lemma AdvEsp :
  forall &m,
    forall (Adv<:Garble.Adv),
      Pr[DkcWorkAdv(AdvGarble.Adv(Adv)).work()@ &m:res] =
        (fold_right (lambda l x, x + (1%r / (borne + 1)%r) * Pr[AdvWork(Adv).work(l)@ &m:res]) (0%r) MeanInt.support)
proof.
  intros &m Adv.
  cut pr : (Pr[MeanInt.Rand(AdvWork(Adv)).randAndWork()@ &m:res] = Pr[DkcWorkAdv(AdvGarble.Adv(Adv)).work()@ &m:res]).
    cut eq : equiv[
      MeanInt.Rand(AdvWork(Adv)).randAndWork ~
      DkcWorkAdv(AdvGarble.Adv(Adv)).work: ((glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){1}=(glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){2})
      ==>res{1}=res{2}].
      fun.
      inline AdvGarble.Adv(Adv).preInit.
      inline AdvWork(Adv).work.
      wp.
      cut prelem : (forall (M<:Dkc.Exp), equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}]);[intros M;fun true;trivial|].
      call ((glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){1}=(glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){2}) (res{1}=res{2}).
      apply (prelem (<:Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv)))).
      wp.
      rnd.
      skip;progress.
    equiv_deno eq;clear eq;progress.
  rewrite <- pr.

cut lem : (forall (f:int -> real -> real) (s:int set),
fold_right f 0%r s =
fold_right (lambda (l : int) (x : real), if in_supp l MeanInt.d then (f l x) else x) 0%r s).
intros f s;elimT Set_ind s;trivial.

rewrite (lem (lambda (l : int) (x : real),
     x + (1%r / (borne + 1)%r) * Pr[AdvWork(Adv).work(l) @ &m : res{hr}])
MeanInt.support).
clear lem.
simplify.

  rewrite (_:
(lambda (l : int) (x : real),
     (if in_supp l MeanInt.d then x + (1%r / (borne + 1)%r) *
     Pr[AdvWork(Adv).work(l) @ &m : res] else x))
=
(lambda (l : int) (x : real),
     x +
     (mu_x MeanInt.d l) *
     Pr[AdvWork(Adv).work(l) @ &m : res])

).
  apply (Fun.extentionality<:real -> real, int>
(lambda (l : int), lambda (x : real),
     (if in_supp l MeanInt.d then x + (1%r / (borne + 1)%r)  *
     Pr[AdvWork(Adv).work(l) @ &m : res] else x))

(lambda (l : int) (x : real),
     x +
     (mu_x MeanInt.d l) *
     Pr[AdvWork(Adv).work(l) @ &m : res])
_
).
intros l.
  apply (Fun.extentionality<:real, real>
(lambda (x : real),
     (if in_supp l MeanInt.d then x + (1%r / (borne + 1)%r)  *
     Pr[AdvWork(Adv).work(l) @ &m : res] else x))

(lambda (x : real),
     x +
     (mu_x MeanInt.d l) *
     Pr[AdvWork(Adv).work(l) @ &m : res])
_
).
intros x.
simplify.
rewrite (_:(x + (mu_x MeanInt.d l)*Pr[AdvWork(Adv).work(l) @ &m : res{hr}]=if in_supp l MeanInt.d then x + 1%r / (borne + 1)%r * Pr[AdvWork(Adv).work(l) @ &m : res{hr}] else x)).
case (in_supp l MeanInt.d).
intros h.
delta MeanInt.d.
rewrite (Dinter.mu_x_def_in 0 borne l _);[trivial|].
rewrite (_:borne - 0 + 1 = borne + 1). trivial.
split.
trivial.
split.
apply (MeanInt.Mean &m (<:AdvWork(Adv))).
save.

lemma DkcEsp :
  forall &m,
    forall (Adv<:Dkc.Adv),
      Pr[Dkc.Game(Dkc.Dkc, Adv).main()@ &m:res] = 
        (Pr[DkcWork(Adv).work(true)@ &m:res] +
           Pr[DkcWork(Adv).work(false)@ &m:res]) / 2%r
proof.
  admit.
save.

lemma RelDkcGarble :
  forall &mDKC,
    forall (Adv<:Garble.Adv),
      forall &mGAR,
      Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &mGAR:res] =
        2%r * borne%r * Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv)).main()@ &mDKC:res]
          + 1%r / 2%r - borne%r
proof.
  admit.
save.

lemma PrvIndGarble :
  forall (epsilon:real),
    forall (Adv<:Garble.Adv), forall &m,
      epsilon > 0%r =>
        Real.abs (Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] - 1&r / 2%r) < epsilon
proof.
  admit.
save.



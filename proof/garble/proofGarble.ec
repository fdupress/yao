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
require import Myset.

lemma prReal :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1 &2,
      (glob ADV){1} = (glob ADV){2} /\
      (Dkc.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=0) =>
    Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work() @ &1 : res] =
      Pr[Garble.Game(Garble.PrvInd(RandGarble), ADV).main() @ &2 : res].
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
      Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work() @ &2 : res].
proof.
  admit.
save.

lemma fakePr :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1,
      (Dkc.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=borne) =>
        Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work()@ &1 : res] = 1%r / 2%r.
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

module DkcWorkAdv(Adv:Dkc.Adv) = {
  module Game = Dkc.Game(Dkc.Dkc, Adv)
  fun work() : bool = {
    var r : bool;
    Adv.preInit();
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

lemma DkcExp : forall (M<:Dkc.Exp),
  equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}].
proof.
intros M;fun true;trivial.
save.

(*
lemma DkcWork :
  forall b,
  forall &m,
    forall (Adv<:Dkc.Adv {Dkc.Dkc}),
      Dkc.Dkc.b{m} = b =>
  Pr[DkcWorkAdv(Adv).work()@ &m:res] = 
    Pr[DkcWork(Adv).work(b)@ &m:res] =
proof.
  intros b &m Adv h.
  cut eq : equiv[DkcWorkAdv(Adv).work ~ DkcWork(Adv).work
: Dkc.Dkc.b{1} = x{2} /\ (glob Adv){1} = (glob Adv){2} /\ (glob Dkc.Game(Dkc.Dkc,Adv)){1} = (glob Dkc.Game(Dkc.Dkc,Adv)){2}
      ==>res{1}=res{2}].
  fun.
  call ((glob Dkc.Game(Dkc.Dkc,Adv)){1} = (glob Dkc.Game(Dkc.Dkc,Adv)){2}) (res{1}=res{2}).
  apply (DkcExp (<:Dkc.Game(Dkc.Dkc,Adv))).
  call ((glob Adv){1} = (glob Adv){2}) (res{1}=res{2}/\(glob Adv){1} = (glob Adv){2}).
  fun true;trivial.
  wp.
  skip. progress.
  equiv_deno eq.
  progress assumption.
  trivial.
save.*)

theory AdvEsp.

op b : bool.

module AdvWork(Adv:Garble.Adv) : MeanInt.Worker = {
  module Game = Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))

  fun work(x:int) : bool = {
    var r : bool;
    AdvGarble.Adv.l = x;
    Dkc.Dkc.b = b;
    r := Game.work();
    return r;
  }
}.

lemma AdvEsp :
  forall &m,
    forall (Adv<:Garble.Adv),
      forall c, c = b =>
      Pr[DkcWork(AdvGarble.Adv(Adv)).work(c)@ &m:res] =
        (sum (lambda l, (1%r / (borne + 1)%r) * Pr[AdvWork(Adv).work(l)@ &m:res]) MeanInt.support).
proof.
  intros &m Adv c h.
  cut pr : (Pr[MeanInt.Rand(AdvWork(Adv)).randAndWork()@ &m:res] = Pr[DkcWork(AdvGarble.Adv(Adv)).work(c)@ &m:res]).
    cut eq : equiv[
      MeanInt.Rand(AdvWork(Adv)).randAndWork ~
      DkcWork(AdvGarble.Adv(Adv)).work: x{2} = c /\ (glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){1}=(glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){2}
      ==>res{1}=res{2}].
      fun.
      inline AdvGarble.Adv(Adv).preInit.
      inline AdvWork(Adv).work.
      wp.
      call ((glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){1}=(glob Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv))){2}) (res{1}=res{2}).
      apply (DkcExp (<:Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv)))).
      wp.
      rnd.
      wp.
      skip. progress assumption.
    equiv_deno eq;progress assumption;trivial.
  rewrite <- pr.

rewrite (sum_in<:int> (lambda (l : int), (1%r / (borne + 1)%r) * Pr[AdvWork(Adv).work(l) @ &m : res{hr}]) MeanInt.support).
simplify.
cut lem : ((lambda (x:int),
(if mem x MeanInt.support then
  1%r / (Int.(+) borne 1)%r * Pr[AdvWork(Adv).work(x) @ &m : res{hr}]
else
  0%r)) = lambda (x:int), (mu_x MeanInt.d x * Pr[AdvWork(Adv).work(x) @ &m :res{hr}])).
delta MeanInt.d.
apply (Fun.extentionality<:real, int> (lambda (x:int),
(if mem x MeanInt.support then
  1%r / (Int.(+) borne 1)%r * Pr[AdvWork(Adv).work(x) @ &m : res{hr}]
else
  0%r)) (lambda (x:int), (mu_x MeanInt.d x * Pr[AdvWork(Adv).work(x) @ &m :res{hr}])) _).
intros x.
case (mem x MeanInt.support = true).
intros hh.
delta MeanInt.d.
rewrite (Dinter.mu_x_def_in 0 borne x _).
trivial.
rewrite (_:borne - 0 + 1 = borne + 1).
trivial.
rewrite hh.
progress.
trivial.
rewrite lem.
apply (MeanInt.Mean &m (<:AdvWork(Adv))).
save.

end AdvEsp.

clone AdvEsp as AdvEspTrue with op b = true.
clone AdvEsp as AdvEspFalse with op b = false.

lemma DkcEsp :
  forall &m,
    forall (Adv<:Dkc.Adv {Dkc.Dkc}),
      Pr[Dkc.Game(Dkc.Dkc, Adv).main()@ &m:res] = 
        (Pr[DkcWork(Adv).work(true)@ &m:res] +
           Pr[DkcWork(Adv).work(false)@ &m:res]) / 2%r
proof.
  intros &m Adv.
  cut pr : (Pr[Dkc.Game(Dkc.Dkc, Adv).main()@ &m:res] = Pr[MeanBool.Rand(DkcWork(Adv)).randAndWork()@ &m:res]).
    cut eq : equiv[
      Dkc.Game(Dkc.Dkc, Adv).main ~
      MeanBool.Rand(DkcWork(Adv)).randAndWork: (glob Adv){1} = (glob Adv){2}/\ (glob Dkc.Game(Dkc.Dkc, Adv)){1}=(glob Dkc.Game(Dkc.Dkc, Adv)){2}
      ==>res{1}=res{2}].
      fun.
      inline Dkc.Game(Dkc.Dkc, Adv).preInit.
      inline Dkc.Dkc.preInit.
      inline DkcWork(Adv).work.
      wp.
      cut prelem : (forall (M<:Dkc.Exp), equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}]);[intros M;fun true;trivial|].
      call ((glob Dkc.Game(Dkc.Dkc, Adv)){1}=(glob Dkc.Game(Dkc.Dkc, Adv)){2}) (res{1}=res{2}).
      apply (prelem (<:Dkc.Game(Dkc.Dkc, Adv))).
      wp.
      call ((glob Adv){1} = (glob Adv){2}) ((glob Adv){1} = (glob Adv){2});[fun true;trivial|].
      wp.
      rnd.
      skip. progress assumption.
    equiv_deno eq;progress assumption;trivial.
  rewrite pr.
  rewrite (MeanBool.Mean &m (<:DkcWork(Adv))).
  trivial.
save.

lemma RelDkcGarble :
  forall &m,
    forall (Adv<:Garble.Adv{Dkc.Dkc}),
      Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] =
        2%r * borne%r * Pr[Dkc.Game(Dkc.Dkc, AdvGarble.Adv(Adv)).main()@ &m:res]
          + 1%r / 2%r - borne%r
proof.
  intros &m Adv.
  rewrite (DkcEsp &m (<:AdvGarble.Adv(Adv))).
  rewrite (AdvEspTrue.AdvEsp &m (<:Adv) true).
  rewrite (AdvEspFalse.AdvEsp &m (<:Adv) false).
cut test : (forall l, Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}] = 1%r - Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : ! res{hr}]).
  apply (MeanInt.Not &m (<:AdvEspFalse.AdvWork(Adv))).
trivial.
  rewrite sum
  admit.
save.

lemma PrvIndGarble :
  forall (epsilon:real),
    forall (Adv<:Garble.Adv), forall &m,
      epsilon > 0%r =>
        Real.abs (Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] - 1&r / 2%r) < epsilon.
proof.
  admit.
save.



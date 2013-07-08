require import FSet. import Interval.
require import Int.
require import Bool.
require import Distr.
require import Real.

require import Hypothesis.
require import Garble.
require import Mean. export MReal.SumSet.
require import ReductionAda.

clone Mean as MeanBool with
  type base = bool,
  op d = Dbool.dbool,
  op support = add false (add true empty)
  proof in_support by smt.

clone Mean as MeanInt with
  type base = int,
  op d = Dinter.dinter 0 (bound-1),
  op support = interval 0 (bound-1)
  proof in_support by smt.

module DkcWorkAdv(Adv:DKC.AdvAda_t) = {
  module Game = DKC.GameAda(DKC.Dkc, Adv)
  module ADV = Adv(DKC.Dkc)
  fun work() : bool = {
    var r : bool;
    ADV.preInit();
    r = Game.work();
    return r;
  }
}.

module DkcWork(Adv:DKC.AdvAda_t) : MeanBool.Worker = {
  module Game = DKC.GameAda(DKC.Dkc, Adv)
  module ADV = Adv(DKC.Dkc)
  fun work(x:bool) : bool = {
    var r : bool;
    DKC.Dkc.b = x;
    ADV.preInit();
    r = Game.work();
    return r;
  }
}.

lemma DkcExp : forall (M<:DKC.Exp),
  equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}].
proof.
intros _;fun true;progress assumption.
save.


lemma DkcWork :
  forall b,
  forall &m,
    forall (Adv<:DKC.AdvAda_t {DKC.Dkc, DKC.Game}),
      DKC.Dkc.b{m} = b =>
  Pr[DkcWorkAdv(Adv).work()@ &m:res] = 
    Pr[DkcWork(Adv).work(b)@ &m:res].
proof.
  intros b &m Adv h.
  cut eq : equiv[DkcWorkAdv(Adv).work ~ DkcWork(Adv).work
: DKC.Dkc.b{1} = x{2} /\ (glob Adv){1} = (glob Adv){2} /\ (glob DKC.GameAda(DKC.Dkc,Adv)){1} = (glob DKC.GameAda(DKC.Dkc,Adv)){2}
      ==>res{1}=res{2}];
  last equiv_deno eq;progress assumption.
  fun.
  call (DkcExp (DKC.GameAda(DKC.Dkc, Adv))).
  call (_:
    (glob Adv){1} = (glob Adv){2} ==>
    (res{1}=res{2}/\(glob Adv){1} = (glob Adv){2})).
  fun true;progress assumption.
  wp.
  skip;progress.
save.

lemma DkcEsp :
  forall &m,
    forall (Adv<:DKC.AdvAda_t {DKC.Dkc, DKC.Game}),
      Pr[DKC.GameAda(DKC.Dkc, Adv).main()@ &m:res] = 
        (Pr[DkcWork(Adv).work(true)@ &m:res] +
           Pr[DkcWork(Adv).work(false)@ &m:res]) / 2%r.
proof.
  intros &m Adv.
  cut pr : (Pr[DKC.GameAda(DKC.Dkc, Adv).main()@ &m:res] = Pr[MeanBool.Rand(DkcWork(Adv)).randAndWork()@ &m:res]).
    cut eq : equiv[
      DKC.GameAda(DKC.Dkc, Adv).main ~
      MeanBool.Rand(DkcWork(Adv)).randAndWork: (glob Adv){1} = (glob Adv){2}/\ (glob DKC.GameAda(DKC.Dkc, Adv)){1}=(glob DKC.GameAda(DKC.Dkc, Adv)){2}
      ==>res{1}=res{2}].
      fun.
      inline DKC.GameAda(DKC.Dkc, Adv).preInit.
      inline DKC.Dkc.preInit.
      inline DkcWork(Adv).work.
      wp.
      cut prelem : (forall (M<:DKC.Exp), equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}]);
        first (intros M;fun true;by progress).
      call (prelem (DKC.GameAda(DKC.Dkc, Adv))).
      call (_:(glob Adv){1} = (glob Adv){2} ==> (glob Adv){1} = (glob Adv){2});first (fun true;by progress).
      wp;rnd;skip;by (progress assumption).
    equiv_deno eq;progress assumption;smt.
  rewrite pr (MeanBool.Mean &m (DkcWork(Adv))).
  delta MeanBool.support.
  (rewrite ! sum_add;first rewrite mem_add /=);first 2 apply mem_empty.
  rewrite sum_nil /=.
  delta MeanBool.d.
  rewrite ! Dbool.mu_x_def MReal.addZ MReal.C /MReal.(+).
  smt.
save.

theory AdvEsp.

  op b : bool.

  module AdvWork(Adv:Garble.Adv) : MeanInt.Worker = {
    module Game = DKC.GameAda(DKC.Dkc, RedAda(Adv))

    fun work(x:int) : bool = {
      var r : bool;
      RedAda.l = x;
      DKC.Dkc.b = b;
      r = Game.work();
      return r;
    }
}.

lemma RemAdvEsp : forall (ADV <: Garble.Adv{AdvAda}),
  forall &1 &2 x, DKC.Dkc.b{1} = b => AdvAda.l{2} = x =>
    Pr[AdvWork(ADV).work(x) @ &1 : res] =
      Pr[GameAda(DKC.Dkc, ADV).work() @ &2 : res].
  admit.
save.

lemma AdvEsp :
  forall &m,
    forall (Adv<:Garble.Adv{DKC.Dkc,AdvAda,DKC.Game}),
      forall c, c = b =>
      Pr[DkcWork(AdvAda(Adv,DKC.Dkc)).work(c)@ &m:res] =
        (sum (lambda l, (1%r / borne%r) * Pr[AdvWork(Adv).work(l)@ &m:res]) MeanInt.support).
proof.
  intros &m Adv c h.
  cut pr : (Pr[MeanInt.Rand(AdvWork(Adv)).randAndWork()@ &m:res] = Pr[DkcWork(AdvGarble.Adv(Adv)).work(c)@ &m:res]).
    cut eq : equiv[
      MeanInt.Rand(AdvWork(Adv)).randAndWork ~
      DkcWork(AdvGarble.Adv(Adv)).work: x{2} = c /\ (glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){1}=(glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){2}
      ==>res{1}=res{2}].
      fun.
      inline AdvGarble.Adv(Adv).preInit.
      inline AdvWork(Adv).work.
      wp.
      call ((glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){1}=(glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){2}) (res{1}=res{2}).
      apply (DkcExp (<:DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv)))).
      wp.
      rnd.
      wp.
      skip;progress assumption.
    equiv_deno eq;progress assumption;smt.
  rewrite <- pr.

rewrite (sum_in<:int> (lambda (l : int), (1%r / borne%r) * Pr[AdvWork(Adv).work(l) @ &m : res{hr}]) MeanInt.support).
simplify.
cut lem : ((lambda (x:int),
(if mem x MeanInt.support then
  1%r / borne%r * Pr[AdvWork(Adv).work(x) @ &m : res{hr}]
else
  0%r)) = lambda (x:int), (mu_x MeanInt.d x * Pr[AdvWork(Adv).work(x) @ &m :res{hr}])).
delta MeanInt.d.
apply (Fun.extensionality<:real, int> (lambda (x:int),
(if mem x MeanInt.support then
  1%r / borne%r * Pr[AdvWork(Adv).work(x) @ &m : res{hr}]
else
  0%r)) (lambda (x:int), (mu_x MeanInt.d x * Pr[AdvWork(Adv).work(x) @ &m :res{hr}])) _).
intros x.
case (mem x MeanInt.support = true);last smt.
intros hh.
delta MeanInt.d.
rewrite (Dinter.mu_x_def_in 0 (borne-1) x _);first smt.
rewrite (_:((borne - 1) - 0) + 1 = borne);first smt.
rewrite hh.
progress.
rewrite lem.
apply (MeanInt.Mean &m (<:AdvWork(Adv))).
save.

end AdvEsp.

clone AdvEsp as AdvEspTrue with op b = true.
clone AdvEsp as AdvEspFalse with op b = false.
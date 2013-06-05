require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.
require import Distr.

require import Dkc.
require import Gate.
require import GarbleTools.
require AdvGate.
require import Rand.

(*require import EquivReal.
require import EquivHybrid.
require import EquivFake.*)

(*lemma test : (1%r > 0%r).*)

axiom math : (forall (a b:real), a = (4%r * (((((a+b) / 2%r)+1%r)-((b+(1%r / 2%r)) / 2%r)) / 2%r)) - (3%r / 2%r)).


clone Rand as RandBool with type base = bool, op d = Dbool.dbool.
clone Rand as RandInt with type base = int, op d = Dinter.dinter 0 1.

module AdvWork(Adv:Gate.Adv) : RandInt.Worker = {
  module Game = Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv))
  fun work(x:int) : bool = {
    var r : bool;
    AdvGate.Adv.l = x;
    r := Game.work();
    return r;
  }
}.

module DkcWork(Adv:Dkc.Adv) : RandBool.Worker = {
  module Game = Dkc.Game(Dkc.Dkc, Adv)
  fun work(x:bool) : bool = {
    var r : bool;
    Dkc.Dkc.b = x;
    Adv.preInit();
    r := Game.work();
    return r;
  }
}.

module DkcWorkAdv(Adv:Gate.Adv) : RandBool.Worker = {
  module Game = AdvWork(Adv)
  fun work(x:bool) : bool = {
    var r : bool;
    var l : int;
    Dkc.Dkc.b = x;
    l = $Dinter.dinter 0 1;
    r := Game.work(l);
    return r;
  }
}.


  axiom Rand :
    forall &m,
      forall (W<:RandBool.Worker),
        Pr[RandBool.RandBit(W).randAndWork()@ &m:res] = 
          (Pr[W.work(false)@ &m:res] + Pr[W.work(true)@ &m:res]) / 2%r.

lemma DkcAdvantage :
  forall (ADVDKC<:Dkc.Adv {Dkc.Dkc}),
  forall &mDKC,
  exists &mDKC1,
  exists &mDKC0,
    Dkc.Dkc.b{mDKC1} /\
    !Dkc.Dkc.b{mDKC0} /\
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:res] =
    (Pr[Dkc.Game(Dkc.Dkc, ADVDKC).work()@ &mDKC1: res] + 1%r -
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).work()@ &mDKC0: !res]) / 2%r
proof.
intros ADV &m.
cut lem : (equiv[
  Dkc.Game(Dkc.Dkc, ADV).main ~ RandBool.RandBit(DkcWork(ADV)).randAndWork :
      (glob ADV){1}=(glob ADV){2} ==> res{1} = res{2}]).
fun.
inline{1} Dkc.Game(Dkc.Dkc, ADV).preInit.
inline{1} Dkc.Dkc.preInit.
inline{2} DkcWork(ADV).work.
wp.
call (Dkc.Dkc.b{1} = Dkc.Dkc.b{2}/\((glob ADV){1}=(glob ADV){2})) (res{1}=res{2}).
  admit.
call ((glob ADV){1}=(glob ADV){2}) ((glob ADV){1}=(glob ADV){2}).
  fun true;trivial.
wp.
rnd.
skip.
trivial.

cut lem2 : (equiv[
  Dkc.Game(Dkc.Dkc, ADV).work ~ DkcWork(ADV).work :
      Dkc.Dkc.b{1}=x{2}/\(glob ADV){1}=(glob ADV){2} ==> res{1} = res{2}]).
admit.

cut lem3 : (
forall &1, Dkc.Dkc.b{1}=true =>
exists &2,
Pr[Dkc.Game(Dkc.Dkc, ADV).work()@ &1: res] = Pr[DkcWork(ADV).work(true)@ &2: res]).
intros &1 h.
equiv_deno lem2.
simplify.

APPARTION D'UN TOP ICI

exists
simplify.
intros x.

admit.
save.

lemma DkcEspTrue :
  forall (Adv <: Gate.Adv),
  forall &mDKCb,
    exists &mDKC0,
    exists &mDKC1,
      Dkc.Dkc.b{mDKC0} /\
      Dkc.Dkc.b{mDKC1}  /\
      AdvGate.Adv.l{mDKC0} = 0 /\
      AdvGate.Adv.l{mDKC1} = 1 /\ 
    Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKCb:res] =
     (Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKC0:res] +
     Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKC1:res]) / 2%r
proof.
admit.
save.

lemma real :
  forall &mDkc,
    forall &mGate,
      forall (Adv <: Gate.Adv),
        AdvGate.Adv.l{mDkc} = 0 => 
        Dkc.Dkc.b{mDkc} => 
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDkc:res] =
          Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &mGate:res]
proof.
intros _ _ ADV _ _.
equiv_deno (realEq (<:ADV));trivial.
save.


lemma middle :
  forall &mDkc1,
    forall &mDkc2,
      forall (Adv <: Gate.Adv),
        !Dkc.Dkc.b{mDkc1} => 
        AdvGate.Adv.l{mDkc1} = 0 => 
        Dkc.Dkc.b{mDkc2} => 
        AdvGate.Adv.l{mDkc2} = 1 => 
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDkc1: !res] =
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDkc2:  res]
proof.
intros _ _ ADV _ _ _ _.
equiv_deno (hybridEq (<:ADV)).
trivial.
intros &1 &2 h.
trivial.
save.

lemma fake :
  forall &m,
  forall (Adv <: Gate.Adv),
        !Dkc.Dkc.b{m} => 
        AdvGate.Adv.l{m} = 1 => 
      Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &m: !res] = 1%r / 2%r
proof.
intros &m Adv _ _.
rewrite <- (fakePr &m (<:Adv)).
equiv_deno (fakeEq (<:Adv));trivial.
save.

lemma DkcEspFalse :
  forall (Adv <: Gate.Adv),
  forall &mDKCb,
    exists &mDKC0,
    exists &mDKC1,
      !Dkc.Dkc.b{mDKC0} /\
      !Dkc.Dkc.b{mDKC1} /\
      AdvGate.Adv.l{mDKC0} = 0 /\
      AdvGate.Adv.l{mDKC1} = 1 /\ 
    Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKCb: !res] =
     (Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKC0: !res] +
     Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKC1: !res]) / 2%r
proof.
admit.
save.

lemma DkcGateRelation :
  forall &mDKC,
    forall (Adv<:Gate.Adv),
    forall &mGAR,
      Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &mGAR:res] =
        4%r * Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] - 3%r / 2%r
proof.
intros &mDKC Adv &mGAR.

elim (DkcAdvantage (<:AdvGate.Adv(Adv)) &mDKC).
intros &mDKC1 &mDKC0 h.
elim h. clear h. intros b1 h.
elim h. clear h. intros b2 rew.
rewrite rew.
clear rew.

elim (DkcEspTrue (<:Adv) &mDKC1).
intros &mDKC10 &mDKC11 h.
elim h. clear h. intros b11 h.
elim h. clear h. intros b12 h.
elim h. clear h. intros l11 h.
elim h. clear h. intros l12 rew.
rewrite rew.
clear rew.

elim (DkcEspFalse (<:Adv) &mDKC0).
intros &mDKC00 &mDKC01 h.
elim h. clear h. intros b01 h.
elim h. clear h. intros b02 h.
elim h. clear h. intros l01 h.
elim h. clear h. intros l02 rew.
rewrite rew.
clear rew.
rewrite (real &mDKC10 &mGAR (<:Adv) _ _);[trivial|trivial|].
rewrite (middle &mDKC00 &mDKC11 (<:Adv) _ _ _ _);[trivial|trivial|trivial|trivial|].
rewrite (fake &mDKC01 (<:Adv) _ _);[trivial|trivial|].
apply (math Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &mGAR:res]
Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work()@ &mDKC11: res]).
save.

lemma PrvIndGarble :
  forall (epsilon:real),
    forall (Adv<:Gate.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &m:res] < epsilon
proof.
intros epsilon Adv &m.
intros epPos.
rewrite (DkcGateRelation &m (<:Adv) &m).
cut lem : (Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m:res] <
epsilon/4%r + 3%r / 8%r).
apply (Dkc.DKCSec (epsilon/4%r + 3%r / 8%r) (<:AdvGate.Adv(Adv)) &m _).
admit.
admit.
save.
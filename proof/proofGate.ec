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

require import EquivReal.
require import EquivHybrid.
require import EquivFake.

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

lemma DkcAdvantage :
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
  exists &mDKC1,
  exists &mDKC0,
    Dkc.Dkc.b{mDKC1} /\
    !Dkc.Dkc.b{mDKC0} /\
    2%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:res] - 1%r =
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).work()@ &mDKC1: res] -
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).work()@ &mDKC0: !res]
proof.
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

lemma DkcGateRelation1 :
  forall &mDKC,
    forall (Adv<:Gate.Adv),
    forall &mGAR,
      2%r * Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] - 1%r
        =
      (2%r * Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &mGAR:res] - 1%r ) / 4%r
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
admit. (*TODO math*)
save.


lemma DKCGateRelation2 :
  forall &mDKC,
    forall (Adv <:Gate.Adv),
    forall &mGAR,
      Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &mGAR:res] <=
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res]
proof.
intros &mDKC Adv &mGAR.
cut intro : (
let a = Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] in
let b = Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &mGAR:res] in
a <= b).
intros a b.
cut lem : (2%r * a - 1%r = (2%r * b - 1%r ) / 6%r);
  [apply (DkcGateRelation1 &mDKC (<:Adv) &mGAR)|].
cut lem2 : (a = b / 6%r + 5%r / 12%r). trivial.
trivial.
trivial.
trivial.
save.


lemma PrvIndGarble :
  forall (epsilon:real),
    forall (Adv<:Gate.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &m:res] <= epsilon
proof.
intros epsilon Adv &m.
intros epPos.
cut trans : (forall (a b c : real), a <= b => b < c => a <= c);[trivial|].
apply (trans Pr[Gate.Game(Gate.PrvInd(RandGate), Adv).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m:res] epsilon _ _).
apply (DKCGateRelation2 &m (<:Adv) &m).
apply (Dkc.DKCSec epsilon (<:AdvGate.Adv(Adv)) &m _).
trivial.
save.
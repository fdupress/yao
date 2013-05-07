require import Real.

require import Dkc.
require import Gate.
require AdvGate.


lemma real :
  forall &mDkc,(*forced b to 1 and l to 1*)
    forall &mGate,
      forall (Adv <: Gate.Adv),
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc:res] =
          Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGate:res]
proof.
admit.
save.

lemma middle :
  forall &mDkc1,(*forced b to 0 and l to 1*)
    forall &mDkc2,(*forced b to 1 and l to 2*)
      forall (Adv <: Gate.Adv),
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc1: !res] =
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc2:  res]
proof.
admit.
save.

lemma fake :
  forall (Adv <: Gate.Adv),
    forall &m,(*forced b to 0 and l to 2*)
      Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m: !res] = 1%r / 2%r
proof.
admit.
save.

lemma DkcAdv :
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
  forall &mDKC1,(*forced b to 1*)
  forall &mDKC0,(*forced b to 0*)
    2%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:res] - 1%r =
 Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC1:res] - Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC0: !res]
proof.
admit.
save.

lemma DkcGateRelation1 :
  forall &mDKC,
    forall (Adv<:Gate.Adv),
    forall &mGAR,
      2%r * Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] - 1%r
        =
      (2%r * Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGAR:res] - 1%r ) / 6%r
proof.
trivial.
admit.
save.

lemma DKCGateRelation2 :
  forall &mDKC,
    forall (ADVGAR<:Gate.Adv),
    forall &mGAR,
      Pr[Gate.Game(Gate.PrvInd, ADVGAR).main()@ &mGAR:res] <= Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv).main()@ &mDKC:res]
proof.
admit.
save.

lemma PrvIndGarble :
  forall (epsilon:real),
    forall (ADV<:Gate.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd, ADV).main()@ &m:res] <= epsilon
proof.
intros epsilon ADV &m.
intros epPos.
cut trans : (forall (a b c : real), a <= b => b <= c => a <= c).
trivial.
apply (trans Pr[Gate.Game(Gate.PrvInd, ADV).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv).main()@ &mDKC:res] epsilon _ _).
admit.
save.
require import Real.

require import Dkc.
require import Gate.
require AdvGate.

require import Scheme.

axiom real :
  forall (Adv <: Scheme.Adv),
    forall &mDkc,(*forced b to 1 and l to 1*)
      forall &mGate,
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(*(Adv)*)).main()@ &mDkc:res] =
          Pr[Gate.Game(Scheme.PrvInd, Adv).main()@ &mGate:res].

axiom middle :
  forall (Adv <: Scheme.Adv),
    forall &mDkc1,(*forced b to 0 and l to 1*)
      forall &mDkc2,(*forced b to 1 and l to 2*)
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(*(Adv)*)).main()@ &mDkc1: !res] =
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(*(Adv)*)).main()@ &mDkc2:  res].

axiom fake :
  forall (Adv <: Scheme.Adv),
    forall &m,(*forced b to 0 and l to 2*)
      Pr[Gate.Game(Scheme.PrvInd, Adv).main()@ &m: !res] = 1%r / 2%r.

axiom DkcAdv :
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
  forall &mDKC1,(*forced b to 1*)
  forall &mDKC0,(*forced b to 0*)
    2%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:res] - 1%r =
 Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC1:res] - Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC0: !res].

axiom DkcGateRelation1 :
  forall &mDKC,
    forall (ADVGAR<:Scheme.Adv),
    forall &mGAR,
      2%r * Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv).main()@ &mDKC:res] - 1%r
        =
      (2%r * Pr[Gate.Game(Scheme.PrvInd, ADVGAR).main()@ &mGAR:res] - 1%r ) / 6%r.

axiom DKCGateRelation2 :
  forall &mDKC,
    forall (ADVGAR<:Scheme.Adv),
    forall &mGAR,
      Pr[Gate.Game(Scheme.PrvInd, ADVGAR).main()@ &mGAR:res] <= Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv).main()@ &mDKC:res].

axiom PrvIndGarble :
  forall (epsilon:real),
    forall (ADV<:Scheme.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Scheme.PrvInd, ADV).main()@ &m:res] <= epsilon.
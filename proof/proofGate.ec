require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.

require import Dkc.
require import Gate.
require import GarbleTools.
require AdvGate.

lemma real :
  forall &mDkc,
    forall &mGate,
      forall (Adv <: Gate.Adv),
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc:(*b /\ l=0 /\*) res] =
          Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGate:res]
proof.
admit.
save.

lemma middle :
  forall &mDkc1,
    forall &mDkc2,
      forall (Adv <: Gate.Adv),
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc1: !res] =
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc2:  res]
proof.
admit.
save.

lemma fake :
  forall &m,
  forall (Adv <: Gate.Adv),
      Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m: (!Dkc.Dkc.b)/\(*(AdvGate.Adv.l=1)/\*)(!res)] = 1%r / 2%r
proof.
intros &m Adv.
rewrite (RandBit &m).
equiv_deno (fakeEq Adv).
save.*)

lemma DkcAdvantage :
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
  forall &mDKC1,
  forall &mDKC0,
    2%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:res] - 1%r =
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC1:Dkc.Dkc.b/\res] -
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC0: !(Dkc.Dkc.b\/res)]
proof.
admit.
save.

lemma DkcTrue :
  forall (b:bool),
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
    3%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:Dkc.Dkc.b/\res] =
     Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:(Dkc.Dkc.b^^b)/\(res^^b) (*/\ (AdvGate.Adv.l{1}=0)*)] +
     Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:(Dkc.Dkc.b^^b)/\(res^^b) (*/\ (AdvGate.Adv.l{1}=1)*)] +
     Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:(Dkc.Dkc.b^^b)/\(res^^b) (*/\ (AdvGate.Adv.l{1}=2)*)]
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
admit.
save.

lemma DKCGateRelation2 :
  forall &mDKC,
    forall (Adv <:Gate.Adv),
    forall &mGAR,
      Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGAR:res] <=
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res]
proof.
intros &mDKC Adv &mGAR.
cut intro : (
let a = Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] in
let b = Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGAR:res] in
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
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] <= epsilon
proof.
intros epsilon Adv &m.
intros epPos.
cut trans : (forall (a b c : real), a <= b => b < c => a <= c);[trivial|].
apply (trans Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m:res] epsilon _ _).
apply (DKCGateRelation2 &m (<:Adv) &m).
apply (Dkc.DKCSec epsilon (<:AdvGate.Adv(Adv)) &m _).
trivial.
save.
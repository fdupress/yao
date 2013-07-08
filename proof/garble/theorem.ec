require import Real.

(*TODO Remove by Section*)
require import Reduction.

(*Hypothesis*)
require import Hypothesis.

(*Definition*)
require import Garble.

(*Lemmas*)
require import CorrectionProof.
require import ReductionProof.

(*Theorem*)
lemma GarbleCorrect :
  forall (f : funct) , functCorrect f =>
  forall (x : random) , randomCorrect f x =>
  forall (i : input) , inputCorrect f i =>
    let (g, ki, ko) = garble x f in
    eval f i = decrypt ko (evalG g (encrypt ki i)) by [].

lemma GarbleSecure :
  exists (epsilon:real), epsilon > 0%r /\
    forall (Adv<:Garble.Adv{DKC.Dkc,DKC.Game,Red}), forall &m,
        `|Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] - 1%r / 2%r| < epsilon by [].
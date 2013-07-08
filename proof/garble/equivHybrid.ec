require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Bool.
require import Array.

require import Hypothesis.
require import GarbleTools.
require import Garble.
require import RedAda.

lemma realEq :
  forall (ADV <: Garble.Adv{ReductionAda, DKC.Dkc, Garble.PrvInd}),
    forall (l:int),
    equiv [
      DKC.GameAda(DKC.Dkc, RedAda(ADV)).work ~
      DKC.GameAda(DKC.Dkc, RedAda(ADV)).work
      : (glob ADV){1} = (glob ADV){2} /\
      (!DKC.Dkc.b{1}) /\ (RedAda.l{1}=l) /\
      (DKC.Dkc.b{2}) /\ (RedAda.l{2}=l+1) ==> res{1} = res{2}
    ].
proof.
admit.
save.
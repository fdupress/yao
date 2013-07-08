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
require import Reduction.
require import ReductionAda.

lemma realEq :
  forall (ADV <: Garble.Adv{Red, DKC.Dkc}),
    equiv [
      DKC.Game(DKC.Dkc, Red(ADV)).main ~
      DKC.GameAda(DKC.Dkc, RedAda(ADV)).main
      : (glob ADV){1} = (glob ADV){2} ==> res{1} = res{2}
    ].
proof.
  admit.
save.

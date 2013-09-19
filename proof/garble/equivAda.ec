require import Bitstring.
require import List.
require import Map.
require import FSet.
require import Pair.
require import Int.
require import Bool.
require import Array.

require import GarbleTools.
require import PreProof.

require import Reduction.
require import ReductionAda.

lemma adaEq :
  forall (ADV <: PrvIndSec.Adv_t{Red, DKCS.Dkc}),
    equiv [
      DKCS.Game(DKCS.Dkc, Red(ADV)).main ~
      DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).main
      : (glob ADV){1} = (glob ADV){2} ==> res{1} = res{2}
    ].
proof strict.
  admit.
save.

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
require import ReductionAda.

lemma hybridEq :
  forall (ADV <: PrvIndSec.Adv_t {RedAda, DKCS.Dkc, PrvIndSec.Game}),
    forall (l:int),
      0 <= l <= Cst.bound - 1 =>
    equiv [
      PreInit(ADV).f ~
      PreInit(ADV).f
      : (glob ADV){1} = (glob ADV){2} /\
      (!vb{1}) /\ (vl{1}=l) /\
      (vb{2}) /\ (vl{2}=l+1) ==> !res{1} = res{2}
    ].
proof strict.
admit.
save.

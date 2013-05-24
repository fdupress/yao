require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.
require import Array.

require import Dkc.
require import GarbleTools.
require AdvGate.
require import Gate.

lemma realEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
      Gate.Game(Gate.PrvInd(RandGate), Adv).main
      :
      (Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) ==> res{1} = res{2}
    ]
proof.

  intros Adv.
  fun.
  inline {1} AdvGate.Adv.gen_queries.
  inline {1} AdvGate.Adv.get_challenge.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  rcondt {1} 8;[admit|].
  rcondf {1} 9;[admit|].
  rcondt {1} 16;[admit|].
  rcondf {1} 17;[admit|].
  inline {1} AdvGate.Adv.compute0.
  inline {1} AdvGate.Adv.gen_queries0.


  inline {2} Gate.PrvInd.garb.
  inline {2} Gate.PrvInd.get_challenge.

  wp.
  app 30 11 : ((gg{1}, AdvGate.Adv.input{1}, tt) = answer{2}).
save.
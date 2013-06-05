require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Bool.
require import Array.
require import Logic.

require import Dkc.
require import GarbleTools.
require import Garble.
require AdvGarble.



lemma realEq :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work ~
      Garble.Game(Garble.PrvInd(RandGarble), ADV).main
      : (glob ADV){1} = (glob ADV){2} /\
      (Dkc.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=0) ==> res{1} = res{2}
    ]
proof.

  intros ADV.
  fun.
  inline {1} AdvGarble.Adv(ADV).gen_queries.
  inline {1} AdvGarble.Adv(ADV).get_challenge.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGarble.Adv(ADV).garble_queries.
  inline {1} AdvGarble.Adv(ADV).garble_answer.
  inline {1} AdvGarble.Adv(ADV).query1.
  inline {1} AdvGarble.Adv(ADV).query2.
  inline {1} AdvGarble.Adv(ADV)._query1.
  inline {1} AdvGarble.Adv(ADV)._query2.
  inline {1} AdvGarble.Adv(ADV).garb.
  inline {1} AdvGarble.Adv(ADV).garbD.
  inline {2} Garble.PrvInd(RandGarble).garb.
  inline {2} Garble.PrvInd(RandGarble).get_challenge.
  inline {2} RandGarble.gen.

  swap{1} 7 -6.

  app 1 1 : (AdvGarble.Adv.query{1} = query{2}).
  call ((glob ADV){1} = (glob ADV){2}) (res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2}).
    fun true;trivial.
  skip;trivial.
  
  case (Garble.queryValid query{2}).

  rcondt {1} 18;[admit|].
  rcondt {1} 33.
  intros &m;kill 26!7. kill 1!24.
wp;skip;trivial.
wp.
while true (AdvGarble.Adv.n + AdvGarble.Adv.q - 1 - AdvGarble.Adv.g). intros z.
wp.
kill 1!4.
skip.
trivial.
if.
  rcondt {2} 1;[intros &m;skip;trivial|].
  
save.
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


op tuple = (true, false).

axiom elim_p :
  forall (p:('a * 'b) -> bool)
    (t:'a*'b) ,
    (forall (a:'a, b:'b), (t = (a,b)) => p (a, b)) =>
    p t.

lemma test : let (l, r) = tuple in l proof.
elimT elim_p tuple. admit. save.



lemma realEq :
  forall (ADV <: Gate.Adv{AdvGate.Adv}),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(ADV)).work ~
      Gate.Game(Gate.PrvInd(RandGate), ADV).main
      : (glob ADV){1} = (glob ADV){2} /\
      (Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) ==> res{1} = res{2}
    ]
proof.

  intros ADV.
  fun.
  inline {1} AdvGate.Adv(ADV).gen_queries.
  inline {1} AdvGate.Adv(ADV).get_challenge.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGate.Adv(ADV).compute0.
  inline {1} AdvGate.Adv(ADV).gen_queries0.
  inline {2} Gate.PrvInd(RandGate).garb.
  inline {2} Gate.PrvInd(RandGate).get_challenge.
  inline {2} RandGate.gen.

  swap{1} 8 -7.
  
  print query{1}.

  app 1 1 : (query{1} = query{2}).
  call ((glob ADV){1} = (glob ADV){2}) (res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2}).
    fun true;trivial.
  skip;trivial.
  
  rcondt {1} 11. admit.
  rcondt {1} 19. admit.
  rcondt {2} 1. admit.
  wp.
  call (answer{1}=answer{2} /\ (glob ADV){1} = (glob ADV){2}) (res{1}=res{2}).
    fun true;trivial.
  
  case (Gate.eval AdvGate.Adv.fc AdvGate.Adv.xc).
    case (Gate.eval AdvGate.Adv.fc (fst AdvGate.Adv.xc, ! snd AdvGate.Adv.xc)).
  
save.
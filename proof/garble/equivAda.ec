require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Bool.
require import Array.

require import Dkc.
require import GarbleTools.
require import Garble.
require AdvGarble.
require AdvGarble_inter.



lemma realEq :
  forall (ADV <: Garble.Adv{AdvGarble.Adv, Dkc.Dkc, AdvGarble_inter.Inter}),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).main ~
      AdvGarble_inter.Game2(Dkc.Dkc, ADV).main
      : (glob ADV){1} = (glob ADV){2} ==> res{1} = res{2}
    ]
proof.

  intros ADV.
  fun.
  inline{1} Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).preInit.
  inline{2} AdvGarble_inter.Game2(Dkc.Dkc, ADV).preInit.
  inline Dkc.Dkc.preInit.
  inline{1} Dkc.Game(Dkc.Dkc, AdvGarble.Adv(ADV)).work.
  inline{2} AdvGarble_inter.Game2(Dkc.Dkc, ADV).work.
  inline AdvGarble.Adv(ADV).gen_queries.
  inline AdvGarble.Adv(ADV).get_challenge.
  inline AdvGarble.Adv(ADV).preInit.

  inline {2} AdvGarble_inter.Game2(Dkc.Dkc, ADV).A.work.
  inline {2} AdvGarble_inter.Inter(ADV, Dkc.Dkc).garble.
  inline {2} AdvGarble_inter.Inter(ADV, Dkc.Dkc).query.
  inline {2} AdvGarble_inter.Inter(ADV, Dkc.Dkc).garbD.
  inline {2} AdvGarble_inter.Inter(ADV, Dkc.Dkc).garb.

  inline {1} AdvGarble.Adv(ADV).garble_queries.
  inline {1} AdvGarble.Adv(ADV).garble_answer.
  inline {1} AdvGarble.Adv(ADV).query1.
  inline {1} AdvGarble.Adv(ADV).query2.
  inline {1} AdvGarble.Adv(ADV).garbD.
  inline {1} AdvGarble.Adv(ADV).garb.

  inline Dkc.Dkc.preInit.
  inline Dkc.Dkc.get_challenge.
  inline Dkc.Dkc.initialize.
  inline Dkc.Dkc.encrypt.

  wp. 

  case (queryValid AdvGarble.Adv.query{1}).
    rcondt{1} 21. admit.
    rcondt{1} 36. admit.
    rcondt{2} 21. admit.
    wp.
    call (answer{1}=answer{2} /\ (glob ADV){1} = (glob ADV){2}) (res{1}=res{2}).
      fun true;smt.
    wp.
    while (
      AdvGarble.Adv.l{1} = AdvGarble_inter.Inter.l{2} /\
      AdvGarble.Adv.aa{1} = AdvGarble_inter.Inter.aa{2} /\
      AdvGarble.Adv.bb{1} = AdvGarble_inter.Inter.bb{2} /\
      AdvGarble.Adv.v{1} = AdvGarble_inter.Inter.v{2} /\
      AdvGarble.Adv.xx{1} = AdvGarble_inter.Inter.xx{2} /\
      AdvGarble.Adv.g{1} = AdvGarble_inter.Inter.g{2} /\
      AdvGarble.Adv.t{1} = AdvGarble_inter.Inter.t{2} /\
      AdvGarble.Adv.pp{1}=AdvGarble_inter.Inter.pp{2} /\
      AdvGarble.Adv.a{1}=AdvGarble_inter.Inter.a{2} /\
      AdvGarble.Adv.b{1}=AdvGarble_inter.Inter.b{2} /\
      rand7{1} = rand3{2}
    ).
    wp.
    app 6 6 : (
      AdvGarble.Adv.l{1} = AdvGarble_inter.Inter.l{2} /\
      AdvGarble.Adv.aa{1} = AdvGarble_inter.Inter.aa{2} /\
      AdvGarble.Adv.bb{1} = AdvGarble_inter.Inter.bb{2} /\
      AdvGarble.Adv.v{1} = AdvGarble_inter.Inter.v{2} /\
      AdvGarble.Adv.xx{1} = AdvGarble_inter.Inter.xx{2} /\
      AdvGarble.Adv.g{1} = AdvGarble_inter.Inter.g{2} /\
      AdvGarble.Adv.t{1} = AdvGarble_inter.Inter.t{2} /\
      AdvGarble.Adv.pp{1}=AdvGarble_inter.Inter.pp{2} /\
      AdvGarble.Adv.a{1}=AdvGarble_inter.Inter.a{2} /\
      AdvGarble.Adv.b{1}=AdvGarble_inter.Inter.b{2} /\
      rand7{1} = rand3{2}
    ). wp. skip. smt.
    if.
    smt.
    wp.
    app 3 3 : (
      AdvGarble.Adv.l{1} = AdvGarble_inter.Inter.l{2} /\
      AdvGarble.Adv.aa{1} = AdvGarble_inter.Inter.aa{2} /\
      AdvGarble.Adv.bb{1} = AdvGarble_inter.Inter.bb{2} /\
      AdvGarble.Adv.v{1} = AdvGarble_inter.Inter.v{2} /\
      AdvGarble.Adv.xx{1} = AdvGarble_inter.Inter.xx{2} /\
      AdvGarble.Adv.g{1} = AdvGarble_inter.Inter.g{2} /\
      AdvGarble.Adv.t{1} = AdvGarble_inter.Inter.t{2} /\
      AdvGarble.Adv.pp{1}=AdvGarble_inter.Inter.pp{2} /\
      AdvGarble.Adv.a{1}=AdvGarble_inter.Inter.a{2} /\
      AdvGarble.Adv.b{1}=AdvGarble_inter.Inter.b{2} /\
      rand7{1} = rand3{2}
    ). wp. skip. intros &1 &2 h. smt.
    if. smt.

    app 3 3 : (
      AdvGarble.Adv.l{1} = AdvGarble_inter.Inter.l{2} /\
      AdvGarble.Adv.aa{1} = AdvGarble_inter.Inter.aa{2} /\
      AdvGarble.Adv.bb{1} = AdvGarble_inter.Inter.bb{2} /\
      AdvGarble.Adv.v{1} = AdvGarble_inter.Inter.v{2} /\
      AdvGarble.Adv.xx{1} = AdvGarble_inter.Inter.xx{2} /\
      AdvGarble.Adv.g{1} = AdvGarble_inter.Inter.g{2} /\
      AdvGarble.Adv.t{1} = AdvGarble_inter.Inter.t{2} /\
      AdvGarble.Adv.pp{1}=AdvGarble_inter.Inter.pp{2} /\
      AdvGarble.Adv.a{1}=AdvGarble_inter.Inter.a{2} /\
      AdvGarble.Adv.b{1}=AdvGarble_inter.Inter.b{2} /\
      rand7{1} = rand3{2}
    ).




  swap{1} 7 -6.

  app 1 1 : (AdvGarble.Adv.query{1} = query{2}).
  call ((glob ADV){1} = (glob ADV){2}) (res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2}).
    fun true;smt.
  skip;smt.
  
  case (Garble.queryValid query{2}).

  rcondt {1} 27;[admit|].
  rcondt {1} 18;[admit|].
  rcondt {2} 1;[intros &m;skip;smt|].
  
save.

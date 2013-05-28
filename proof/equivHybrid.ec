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

lemma hybridEq :
      forall (Adv <: Gate.Adv),
        equiv [
          Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
            Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
          (!Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) /\
          (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{2}=1)
          ==> !res{1} = res{2}
        ]
proof.
  intros Adv.
  fun.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGate.Adv(Adv).gen_queries.
  inline {1} AdvGate.Adv(Adv).get_challenge.
  inline {1} AdvGate.Adv(Adv).compute0.
  inline {1} AdvGate.Adv(Adv).gen_queries0.
  inline {2} Dkc.Dkc.preInit.
  inline {2} Dkc.Dkc.get_challenge.
  inline {2} Dkc.Dkc.initialize.
  inline {2} Dkc.Dkc.encrypt.
  inline {2} AdvGate.Adv(Adv).gen_queries.
  inline {2} AdvGate.Adv(Adv).get_challenge.
  inline {2} AdvGate.Adv(Adv).compute1.
  inline {2} AdvGate.Adv(Adv).gen_queries1.
 
  swap [7..9] -6.

  app 3 3 : (
    AdvGate.Adv.c{1} = AdvGate.Adv.c{2} /\
    AdvGate.Adv.fc{1} = AdvGate.Adv.fc{2} /\
    AdvGate.Adv.xc{1} = AdvGate.Adv.xc{2} /\
    query{1} = query{2} /\
    AdvGate.Adv.l{1}=0 /\
    Dkc.Dkc.b{1} = false /\
    AdvGate.Adv.l{2}=1 /\
    Dkc.Dkc.b{2} = true
  );[wp;call true (res{1}=res{2});[admit|rnd;skip;trivial]|]. (* Call adv gen_queries *)

  case (Gate.eval (fst (fst query{2})) (snd (fst query{2})) = Gate.eval (fst (snd query{2})) (snd (snd query{2}))). (*good*)

  rcondt {1} 9;[intros &m;wp;rnd;wp;rnd;skip;trivial|]. (*good*)
  rcondf {1} 11;[admit|]. (* l condition *)
  rcondt {1} 10;[admit|]. (* l condition *)
  rcondt {1} 17;[admit|]. (* While *)
  rcondt {1} 24;[admit|]. (* While *)
  rcondf {1} 31;[admit|]. (* While *)
  rcondt {1} 33;[admit|]. (* good *)
  rcondf {1} 34;[admit|]. (* l *)
  rcondt {1} 33;[admit|]. (* l *)

  rcondt {2} 9;[intros &m;wp;rnd;wp;rnd;skip;trivial|]. (*good*)
  rcondf {2} 10;[admit|]. (* l condition *)
  rcondt {2} 10;[admit|]. (* l condition *)
  rcondt {2} 18;[admit|]. (* While *)
  rcondt {2} 25;[admit|]. (* While *)
  rcondf {2} 32;[admit|]. (* While *)
  rcondt {2} 34;[admit|]. (* good *)
  rcondf {2} 34;[admit|]. (* l *)
  rcondt {2} 34;[admit|]. (* l *)

  wp.
  call (answer{1}=answer{2}) (res{1} = res{2});[admit|].
  wp.
  swap{1} [5..6] -3. (*rewrite tau*)
  swap{1} 9 -5. (*rewrite tau*)
  swap{1} 10 -5. (*t*)
  swap{1} 38 -32. (*keyntau*)

  swap{2} 10 -9. (*t*)

  swap{1} [6..7] -2. (*rewrite tau*)
  swap{1} 10 -5. (*rewrite tau*)
  swap{2} 39 -30. (*key_nt_ntau*)
  swap{2} 39 -25. (*keyntau*)
  swap{1} 38 -25. (*keyntau*)
  swap{1} 10 -8. (*t*)
  swap{2} 11 -10. (*t*)


  case (
(Gate.eval AdvGate.Adv.fc{1} AdvGate.Adv.xc{1}=Gate.eval AdvGate.Adv.fc{1} (!(fst AdvGate.Adv.xc{1}), (snd AdvGate.Adv.xc{1}))) /\
(Gate.eval AdvGate.Adv.fc{2} AdvGate.Adv.xc{2}=Gate.eval AdvGate.Adv.fc{2} (!(fst AdvGate.Adv.xc{2}), (snd AdvGate.Adv.xc{2})))
).
  rcondt{1} 37;[admit|].
  rcondt{1} 38;[admit|].
  rcondt{2} 39;[admit|].
  wp.

  (*BEGIN CLEAN DKC*)
  (*LOOP 2*)
  (rcondt {1} 28;[admit|]). (* Dkc used *)
  (rcondt {1} 29;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 30;[admit|]). (* Dkc not reusing *) (*TODO: FALSE*)
  (rcondt {1} 31;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 30;[admit|]). (* Dkc used *)
  (rcondt {2} 31;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 32;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 33;[admit|]). (* Dkc not reusing *)
  (*LOOP 1*)
  (rcondt {1} 21;[admit|]). (* Dkc used *)
  (rcondt {1} 22;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 23;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 24;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 23;[admit|]). (* Dkc used *)
  (rcondt {2} 24;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 25;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 26;[admit|]). (* Dkc not reusing *)
  (*END CLEAN DKC*)

  wp.

  rnd.
  rnd.
  swap{2} 37 -34.
save.
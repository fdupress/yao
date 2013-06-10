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
      forall (Adv <: Gate.Adv{Dkc.Dkc, AdvGate.Adv}),
        equiv [
          Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
            Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
          (glob Adv){1} = (glob Adv){2} /\
          (!Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) /\
          (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{2}=1)
          ==> !res{1} = res{2}
        ].
proof.
  intros Adv.
  fun.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} AdvGate.Adv(Adv).gen_queries.
  inline {1} AdvGate.Adv(Adv).get_challenge.
  inline {1} AdvGate.Adv(Adv).compute0.
  inline {1} AdvGate.Adv(Adv).gen_queries0.
  inline {2} Dkc.Dkc.preInit.
  inline {2} Dkc.Dkc.get_challenge.
  inline {2} Dkc.Dkc.initialize.
  inline {2} AdvGate.Adv(Adv).gen_queries.
  inline {2} AdvGate.Adv(Adv).get_challenge.
  inline {2} AdvGate.Adv(Adv).compute1.
  inline {2} AdvGate.Adv(Adv).gen_queries1.
 
  swap [7..9] -6.

  app 3 3 : (
    (glob Adv){1} = (glob Adv){2} /\
    AdvGate.Adv.c{1} = AdvGate.Adv.c{2} /\
    AdvGate.Adv.fc{1} = AdvGate.Adv.fc{2} /\
    AdvGate.Adv.xc{1} = AdvGate.Adv.xc{2} /\
    query{1} = query{2} /\
    AdvGate.Adv.l{1}=0 /\
    Dkc.Dkc.b{1} = false /\
    AdvGate.Adv.l{2}=1 /\
    Dkc.Dkc.b{2} = true
  );
[wp;call ((glob Adv){1} = (glob Adv){2}) ((glob Adv){1} = (glob Adv){2}/\res{1}=res{2});
[fun true|rnd;skip];trivial|]. (* Call adv gen_queries *)

  case (Gate.queryValid query{1}). (*good*)

  rcondt {1} 9;[intros &m;wp;rnd;wp;rnd;skip;trivial|]. (*good*)
  rcondf {1} 11;[admit|]. (* l condition *)
  rcondt {1} 10;[admit|]. (* l condition *)
  rcondt {1} 17;[intros &m;wp;rnd;wp;rnd;rnd;skip;admit|]. (* While *)
  rcondt {1} 20;[admit|]. (* While *)
  rcondf {1} 23;[admit|]. (* While *)
  rcondt {1} 25;[admit|]. (* good *)
  rcondf {1} 26;[admit|]. (* l *)
  rcondt {1} 25;[admit|]. (* l *)

  rcondt {2} 9;[intros &m;wp;rnd;wp;rnd;skip;trivial|]. (*good*)
  rcondf {2} 10;[admit|]. (* l condition *)
  rcondt {2} 10;[admit|]. (* l condition *)
  rcondt {2} 18;[admit|]. (* While *)
  rcondt {2} 21;[admit|]. (* While *)
  rcondf {2} 24;[admit|]. (* While *)
  rcondt {2} 26;[admit|]. (* good *)
  rcondf {2} 26;[admit|]. (* l *)
  rcondt {2} 26;[admit|]. (* l *)

  inline {1} Dkc.Dkc.encrypt.
  inline {2} Dkc.Dkc.encrypt.

  (*BEGIN CLEAN DKC*)
  (*LOOP 1*)
  (rcondt {1} 20;[admit|]). (* Dkc used *)
  (rcondt {1} 21;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 22;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 23;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 21;[admit|]). (* Dkc used *)
  (rcondt {2} 22;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 23;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 24;[admit|]). (* Dkc not reusing *)
  (*LOOP 2*)
  (rcondt {1} 33;[admit|]). (* Dkc used *)
  (rcondt {1} 34;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 35;[admit|]). (* Dkc not reusing *) (*TODO: FALSE*)
  (rcondt {1} 36;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 34;[admit|]). (* Dkc used *)
  (rcondt {2} 35;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 36;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 37;[admit|]). (* Dkc not reusing *)
  (*END CLEAN DKC*)

  wp.
  call ((glob Adv){1} = (glob Adv){2}/\answer{1}=answer{2}) (res{1}=res{2}).
    fun true;trivial.
  wp.
  (*
  alias {1} 1 with _tau.
  alias {1} 3 with _keytau.
  alias {1} 12 with _t;swap {1} 12 -10.
  alias {1} 24 with _keyt;swap {1} 24 -15.
  alias {1} 25 with _key_tau_t;swap {1} 25 -25.

  alias {2} 1 with nt.*)

  (*init vals*)
  swap [3..4] -2. (*maps*)
  swap{1} [15..16] -12. (*i answers*)
  swap{2} [16..17] -13. (*i answers*)
  swap [9..10] -4. (*query*)
  swap{1} 14 -13. (*good*)
  swap{2} 15 -14. (*good*)
  
  (*tau{1}*)
  swap{1} [10..12] -1. (*rewrite tau*)
  swap{2} 13 -5. (*t*)

  (*t{1}*)
  swap{1} 13 -1. (*t*)
  swap{2} [11..13] -1. (*rewrite tau*)


  swap{1} [29..33] -8. (*init loop*)
  swap{2} [30..34] -8. (*init loop*)

  (*keytau{1}*)
  swap{1} 13 12. (*keytau*)
  alias{2} 35 with _keytau.
  swap{2} 35 -8. (*keynt*)

  (*keyt{1}*)
  swap{2} 51 -23. (*keyntau*)

  (*keyt{1}*)
  swap{2} 51 -23. (*keyntau*)
  

  (*t{1}*)


  swap{2} 10 -9. (*t*)
  swap{2} [6..7] -3. (*rewrite tau*)
  swap{2} 10 -5. (*rewrite tau*)





  swap{2} 38 -31. (*keyntau*)

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
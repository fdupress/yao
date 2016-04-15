(** Security definitions for a two-party protocol *)

require import Bool.
require import DBool.
require import Pair.
require import Real.
require import Distr.

require import Prot.

(**
   The security of a two-party protocol is defined in the semi-honest (honest
   but curious) setting. In this setting, an adversary aim is to distinguish 
   between a real execution of a protocol and a simulated execution. The
   protocol is secure for semi-honest adversaries if the adversary is not able to
   distinguish between the real execution of the protocol and some simulation of
   the protocol.
*)
theory ProtSecurity.
  clone import Protocol.

  (** Correctness assertion *)
  (** 
     A two-party protocol is correct if (ev_1(I_1, I_2), ev_2(I_1, I_2)) = 
     (\Pi_1(I_1), \Pi_2(I_2)). In our model, the elements of the equality are
     captured by operations f and prot.
  *)
  pred Correct (x:unit) = forall i1 r1 i2 r2, 
    validInputs i1 i2 =>
    validRands i1 i2 r1 r2 =>
    f i1 i2 = snd (prot i1 r1 i2 r2).

  (** Views of the parties *)
  (**
     The view of some party is obtained by running the View algorithm. 
     View takes as input the inputs of both parties (I_1, I_2), chooses random
     coins (w_1, w_2) for each party, executes the interation between P1 and P2
     and returns (w_i, conv), where conv is the sequence of messagens exchanged 
     by the two parties.
  *)
  type view1_t = rand1_t * conv_t.
  type view2_t = rand2_t * conv_t.

  (** Random generators *)
  (** We formalise the random generators to produce a random value on input of the leakage *)
  module type Rand1_t = {
    proc gen(i1info : leak1_t) : rand1_t
  }.
  
  module type Rand2_t = {
    proc gen(i2info : leak2_t) : rand2_t
  }.

  (** Simulator *)
  (**
     A simulator is defined for both parties.

     A simulator must simulate the execution of a two-party protocol for a party, with 
     respect to the input of that party, the expected output and the leakage of the
     input of the other party. The output of the simulator is an execution of the protocol (a view)
     that would produce the expected output of the party given its input and with information
     of the input of the other party.

     The intuition behind this definition is that the existance of a successful simulator
     establishes that the views of the parties cannot possibly release more information
     about their inputs in addition to the information received by the simulator (evaluation
     output and admissible leakage).
  *)
  module type Sim_t = {
    proc sim1(i1: input1_t, o1: output1_t, l2: leak2_t) : view1_t
    proc sim2(i2: input2_t, o2: output2_t, l1: leak1_t) : view2_t
  }.

  (** Adversaries *)
  (**
     An adversary is defined for both parties.

     The adversary starts by producing the two inputs to the protocol. After,
     in input of a view, it will try to distinguish if the view was generated
     from a real execution of the protocol or from a simulated execution.
     The adversary prodedures will be used to try to break the security
     of a two-party protocol.
  *)
  module type Adv1_t = { 
    proc gen_query() : input1_t * input2_t
    proc dist(view: view1_t) : bool 
  }.

  module type Adv2_t = {
    proc gen_query() : input1_t * input2_t
    proc dist(view: view2_t) : bool 
  }.

  (** Cryptographic games *)
  (**
     The cryptographic games are used to define the security of both parties.

     These games will use the adversary defined above (that attacks the security
     of the honest-but-curious assumption) to try to break the security of a 
     two-party protocol.

     Each routine starts by using the adversary to produce two inputs that will
     be used during the attack. After, it will choose a random bit which will be used
     to determine if the real execution fo the protocol will take place of if 
     it will be a simulated execution instead. Finally, the routine uses the adversary
     to distinguish if the resulting view is from a real execution of the protocol
     or if it is from a simulated one.
  *)
  module Game1(R1: Rand1_t, R2: Rand2_t, S: Sim_t, A1: Adv1_t) = {
    proc game(b:bool) : bool = {
      var guess : bool;
      var view1 : view1_t;
      var o1 : output1_t;
      var r1 : rand1_t;
      var r2 : rand2_t;
      var i1 : input1_t;
      var i2 : input2_t;
    
      (i1,i2) = A1.gen_query();

      if (!validInputs i1 i2)
        guess = ${0,1};
      else {
        if (b) {
          r1 = R1.gen(phi1 i1);
          r2 = R2.gen(phi2 i2);
          view1 = (r1, fst (prot i1 r1 i2 r2));
        } else {
          o1 = fst (f i1 i2);
          view1 = S.sim1 (i1, o1, phi2(i2));
        }       
        guess = A1.dist(view1);
      }
      return guess=b;
    }
    proc main() : bool = {
      var real, adv: bool;
      real = ${0,1};
      adv = game(real);
      return adv;
    }
  }.

  module Game2(R1: Rand1_t, R2: Rand2_t, S: Sim_t, A2: Adv2_t) = {
    proc game(b: bool) : bool = {
      var i1 : input1_t;
      var i2 : input2_t;
      var guess : bool;
      var view2 : view2_t;
      var o2 : output2_t;
      var r1 : rand1_t;
      var r2 : rand2_t;
    
      (i1,i2) = A2.gen_query();
      
      if (!validInputs i1 i2) {
        guess = ${0,1};
      } else {
        if (b) {
          r1 = R1.gen(phi1 i1);
          r2 = R2.gen(phi2 i2);
          view2 = (r2, fst (prot i1 r1 i2 r2));
        } else {
          o2 = snd (f i1 i2);
          view2 = S.sim2 (i2, o2, phi1(i1));      
        }  
        guess = A2.dist(view2);
      }
      return guess=b;
    }
    proc main() : bool = {
      var real, adv: bool;
      real = ${0,1};
      adv = game(real);
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)

  lemma Game1game_lossless (A1 <: Adv1_t) (S <: Sim_t{A1})
                           (R1 <: Rand1_t {A1}) (R2 <: Rand2_t {A1,R1}) :
    islossless A1.gen_query =>
    islossless A1.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim1 =>
    islossless Game1(R1, R2, S, A1).game.
  proof.
    move => A1gen_ll A1dist_ll R1gen_ll R2gen_ll Ssim1_ll.
    proc => //.
    seq 1: true=> //; first by call (_:true).
    if.
    (*!validInpus*)
      by rnd; skip; smt.
    (*validInputs*)
      if.
      (*b*) 
        call (_:true); first by apply A1dist_ll.
        wp.
        call (_:true); first by apply R2gen_ll.
        call (_:true); first by apply R1gen_ll.
        by skip; smt.
    (*!b*)
        call (_:true); first by apply A1dist_ll.
        call (_:true); first by apply Ssim1_ll.
        by wp; skip; smt.
  qed.

  lemma Game1main_lossless (A1 <: Adv1_t) (S <: Sim_t{A1})
                           (R1 <: Rand1_t {A1}) (R2 <: Rand2_t {A1,R1}) :
    islossless A1.gen_query =>
    islossless A1.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim1 =>
    islossless Game1(R1, R2, S, A1).main.
  proof.
    move => A1gen_ll A1dist_ll R1gen_ll R2gen_ll Ssim1_ll.
    proc => //.
    seq 1: true => //; first by rnd; skip; smt. 
    call (_:true); last by trivial.
    seq 1: true=> //; first by call (_:true).
    if.
    (*!validInpus*)
      by rnd; skip; smt.
    (*validInputs*)
      if.
      (*b*) 
        call (_:true); first by apply A1dist_ll.
        wp.
        call (_:true); first by apply R2gen_ll.
        call (_:true); first by apply R1gen_ll.
        by skip; smt.
      (*!b*)
        call (_:true); first by apply A1dist_ll.
        call (_:true); first by apply Ssim1_ll.
        by wp; skip; smt.
  qed.

  lemma Game2game_lossless (A2 <: Adv2_t) (S <: Sim_t{A2})
                           (R1 <: Rand1_t {A2}) (R2 <: Rand2_t {A2,R1}) :
    islossless A2.gen_query =>
    islossless A2.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim2 =>
    islossless Game2(R1, R2, S, A2).game.
  proof.
    move => A2gen_ll A2dist_ll R1gen_ll R2gen_ll Ssim2_ll.
    proc => //.
    seq 1: true=> //; first by call (_:true).
    if.
    (*!validInpus*)
      by rnd; skip; smt.
    (*validInputs*)
      if.
      (*b*) 
        call (_:true); first by apply A2dist_ll.
        wp.
        call (_:true); first by apply R2gen_ll.
        call (_:true); first by apply R1gen_ll.
        by skip; smt.
      (*!b*)
        call (_:true); first by apply A2dist_ll.
        call (_:true); first by apply Ssim2_ll.
        by wp; skip; smt.
  qed.

  lemma Game2main_lossless (A2 <: Adv2_t) (S <: Sim_t{A2})
                           (R1 <: Rand1_t {A2}) (R2 <: Rand2_t {A2,R1}) :
    islossless A2.gen_query =>
    islossless A2.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim2 =>
    islossless Game2(R1, R2, S, A2).main.
  proof.
    move => A2gen_ll A2dist_ll R1gen_ll R2gen_ll Ssim2_ll.
    proc => //.
    seq 1: true => //; first by rnd; skip; smt. 
    call (_:true); last by trivial.
    seq 1: true=> //; first by call (_:true).
    if.
    (*!validInpus*)
      by rnd; skip; smt.
    (*validInputs*)
      if.
      (*b*) 
        call (_:true); first by apply A2dist_ll.
        wp.
        call (_:true); first by apply R2gen_ll.
        call (_:true); first by apply R1gen_ll.
        by skip; smt.
      (*!b*)
        call (_:true); first by apply A2dist_ll.
        call (_:true); first by apply Ssim2_ll.
        by wp; skip; smt.
  qed.

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)
  
  (**
     The advantage of an adversary against a two-party protocol with respect
     to the games above is |2*Pr[adv = real] - 1|. The two party-protocol
     is secure in the presence of semi-honest adversaries if the advantage is
     negligeble.
      
     The probability Pr[adv = real] can be expandaded as 1/2 * (Pr[adv = real | real = true]
     + Pr[adv = real | real = false]).

     This advantage can be defined in the form of conditional probabilities as
     Pr[adv = real | real = true] - Pr[adv != real | real = false].
  *)
  
  (** Conditional probability expansion Game1 *)
  lemma Game1_xpnd &m (A1 <: Adv1_t) (S <: Sim_t{A1})
                      (R1 <: Rand1_t {A1}) (R2 <: Rand2_t {A1,R1}):
    islossless A1.gen_query =>
    islossless A1.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim1 =>
    Pr[Game1(R1,R2,S,A1).main()  @ &m: res]
    = 1%r/2%r * (Pr[Game1(R1,R2,S,A1).game(true)  @ &m: res]
      + Pr[Game1(R1,R2,S,A1).game(false)  @ &m: res]).
  proof.
    move => A1gen_ll A1dist_ll R1gen_ll R2gen_ll Ssim1_ll.
    pose p1 := Pr[Game1(R1, R2, S, A1).game(true) @ &m : res].
    pose p2 := Pr[Game1(R1, R2, S, A1).game(false) @ &m : res].
    byphoare (_: (glob A1) = (glob A1){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m} ==> _) => //.
    proc => //.
    seq 1: real (1%r/2%r) p1 (1%r/2%r) p2 ((glob A1) = (glob A1){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m}); trivial.
      by auto.
      by rnd; skip; smt.
      call (_: ((glob A1) = (glob A1){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m}) /\ b ==> res)=> //.
        rewrite /p1.
        bypr=> &m' [eqA] b'.
      byequiv (_: ={glob A1, glob S, glob R1, glob R2, b} /\ b{1} ==> ={res})=> //.
        by sim.
        by rewrite b' eqA.
      by rnd; skip; smt.
      call (_: ((glob A1) = (glob A1){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m}) /\ !b ==> res)=> //.
        rewrite /p2.
        bypr=> &m' [eqA] b'.
        byequiv (_: ={glob A1, glob S, glob R1, glob R2, b} /\ !b{1} ==> ={res})=> //.
        by sim.
        by rewrite -neqF; rewrite b'; rewrite eqA.
    by smt.
  qed.

  (** Conditional probability expansion Game2 *)
  lemma Game2_xpnd &m (A2 <: Adv2_t) (S <: Sim_t{A2})
                      (R1 <: Rand1_t {A2}) (R2 <: Rand2_t {A2,R1}):
    islossless A2.gen_query =>
    islossless A2.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim2 =>
    Pr[Game2(R1,R2,S,A2).main()  @ &m: res]
    = 1%r/2%r * (Pr[Game2(R1,R2,S,A2).game(true)  @ &m: res]
      + Pr[Game2(R1,R2,S,A2).game(false)  @ &m: res]).
  proof.
    move => A2gen_ll A2dist_ll R1gen_ll R2gen_ll Ssim2_ll.
    pose p1 := Pr[Game2(R1, R2, S, A2).game(true) @ &m : res].
    pose p2 := Pr[Game2(R1, R2, S, A2).game(false) @ &m : res].
    byphoare (_: (glob A2) = (glob A2){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m} ==> _) => //.
    proc => //.
    seq 1: real (1%r/2%r) p1 (1%r/2%r) p2 ((glob A2) = (glob A2){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m}); trivial.
      by auto.
      by rnd; skip; smt.
      call (_: ((glob A2) = (glob A2){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m}) /\ b ==> res)=> //.
        rewrite /p1.
        bypr=> &m' [eqA] b'.
      byequiv (_: ={glob A2, glob S, glob R1, glob R2, b} /\ b{1} ==> ={res})=> //.
        by sim.
        by rewrite b' eqA.
      by rnd; skip; smt.
      call (_: ((glob A2) = (glob A2){m} /\ (glob S) = (glob S){m} /\ (glob R1) = (glob R1){m} /\ (glob R2) = (glob R2){m}) /\ !b ==> res)=> //.
        rewrite /p2.
        bypr=> &m' [eqA] b'.
        byequiv (_: ={glob A2, glob S, glob R1, glob R2, b} /\ !b{1} ==> ={res})=> //.
        by sim.
        by rewrite -neqF; rewrite b'; rewrite eqA.
    by smt.
  qed.

  (** Advantage definition Game1 *)
  lemma Game1_adv &m (A1 <: Adv1_t) (S <: Sim_t{A1})
                     (R1 <: Rand1_t {A1}) (R2 <: Rand2_t {A1,R1}):
    islossless A1.gen_query =>
    islossless A1.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim1 =>
    2%r * Pr[Game1(R1,R2,S,A1).main()  @ &m: res] - 1%r
    = Pr[Game1(R1,R2,S,A1).game(true)  @ &m: res] 
      - Pr[Game1(R1,R2,S,A1).game(false)  @ &m: !res].
  proof.
    move=> A1gen_ll A1dist_ll R1gen_ll R2gen_ll Ssim1_ll.
    rewrite Pr [mu_not].
    pose p1:= Pr[Game1(R1,R2,S,A1).game(true) @ &m : res].
    pose p2:= Pr[Game1(R1,R2,S,A1).game(false) @ &m : res]. 
    cut ->: Pr[Game1(R1,R2,S,A1).game(false) @ &m : true] = 1%r. 
      byphoare (_: true)=> //.
      by apply (Game1game_lossless A1 S R1 R2). 
    cut Hp1: phoare [Game1(R1,R2,S,A1).game:
                    (glob Game1(R1,R2,S,A1)) = (glob Game1(R1,R2,S,A1)){m} /\ b ==> res] = p1.
      bypr=> &m' [eqG] b'; rewrite /p1 b'.
      by byequiv (_: ={glob Game1(R1,R2,S,A1), b} ==> ={res})=> //; sim.
    cut Hp2: phoare [Game1(R1,R2,S,A1).game:
                   (glob Game1(R1,R2,S,A1)) = (glob Game1(R1,R2,S,A1)){m} /\ !b ==> res] = p2.
      bypr=> &m' [eqG]; rewrite -neqF=> b'; rewrite /p2 b'.
      by byequiv (_: ={glob Game1(R1,R2,S,A1), b} ==> ={res})=> //; first sim; sim.
    cut Hp: phoare [Game1(R1,R2,S,A1).main:
              (glob Game1(R1,R2,S,A1)) = (glob Game1(R1,R2,S,A1)){m} ==> res] = ((p1+p2)/2%r).
      proc => //.
      seq 1: real (1%r / 2%r) p1 (1%r / 2%r) p2
             ((glob Game1(R1,R2,S,A1)) = (glob Game1(R1,R2,S,A1)){m}).
        by auto.
        by rnd ((=) true); skip; smt.
        by call Hp1.
        by rnd ((=) false); skip; smt.
        by call Hp2.
        by smt.
    cut ->: Pr[Game1(R1,R2,S,A1).main() @ &m : res] = ((p1+p2)/2%r).
      by byphoare Hp.
    by smt.
  qed.

  (** Advantage definition Game2 *)
  lemma Game2_adv &m (A2<:Adv2_t {Game2}) (S<:Sim_t {A2}) (R1<:Rand1_t {A2}) (R2<:Rand2_t {A2,R1}):
    islossless A2.gen_query =>
    islossless A2.dist =>
    islossless R1.gen =>
    islossless R2.gen =>
    islossless S.sim2 =>
    2%r * Pr[Game2(R1,R2,S,A2).main()  @ &m: res] - 1%r
    = Pr[Game2(R1,R2,S,A2).game(true)  @ &m: res] 
      - Pr[Game2(R1,R2,S,A2).game(false)  @ &m: !res].
  proof.
    move=> A2gen_ll A2dist_ll R1gen_ll R2gen_ll Ssim2_ll.
    rewrite Pr [mu_not].
    pose p1:= Pr[Game2(R1,R2,S,A2).game(true) @ &m : res].
    pose p2:= Pr[Game2(R1,R2,S,A2).game(false) @ &m : res].
    cut ->: Pr[Game2(R1,R2,S,A2).game(false) @ &m : true] = 1%r.
      byphoare (_:true)=> //.
      by apply (Game2game_lossless A2 S R1 R2). 
    cut Hp1: phoare [Game2(R1,R2,S,A2).game:
                       (glob Game2(R1,R2,S,A2)) = (glob Game2(R1,R2,S,A2)){m} /\ b ==> res] = p1.
      bypr=> &m' [eqG] b'; rewrite /p1 b'.
      byequiv (_: ={glob Game2(R1,R2,S,A2), b} ==> ={res})=> //; first by sim.
    cut Hp2: phoare [Game2(R1,R2,S,A2).game:
                       (glob Game2(R1,R2,S,A2)) = (glob Game2(R1,R2,S,A2)){m} /\ !b ==> res] = p2.
      bypr=> &m' [eqG]; rewrite -neqF=> b'; rewrite /p2 b'.
      byequiv (_: ={glob Game2(R1,R2,S,A2), b} ==> ={res})=> //; first by sim.
    cut Hp: phoare [Game2(R1,R2,S,A2).main:
                      (glob Game2(R1,R2,S,A2)) = (glob Game2(R1,R2,S,A2)){m} ==> res] = ((p1+p2)/2%r).
      proc => //.
      seq 1: real (1%r / 2%r) p1 (1%r / 2%r) p2
             ((glob Game2(R1,R2,S,A2)) = (glob Game2(R1,R2,S,A2)){m}).
        by auto.
        by rnd ((=) true); skip; smt.
        by call Hp1.
        by rnd ((=) false); skip; smt.
        by call Hp2.
        by smt.
    cut ->: Pr[Game2(R1,R2,S,A2).main() @ &m : res] = ((p1+p2)/2%r).
      by byphoare Hp.
    by smt.
  qed.

end ProtSecurity.
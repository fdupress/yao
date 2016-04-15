(** Secure function evaluation (SFE) *)

require import Pair Int Real Array Distr.

require import ArrayExt.

require (*--*) ProjSch SchSec.
require (*--*) OT OTSec.
require (*--*) Prot ProtSec.

(** 
  In a SFE protocol, party P1 wants to evaluate some public function with respect
  to its own input and to the input of party P2. The protocol must ensure that P1
  learns nothing about the input of P2.

  In a PFE protocol, P1 wants to evaluate some private function that possesses 
  with respect to its own input and to the input of P2. The protocol must ensure that
  P1 learns nothing about the private function and about the input of P2.
  
  Theory SFE defines a two-party protocol for either "Secure Function Evaluation"
  (SFE) or "Private Function Evaluation" (PFE). The protocol is built on top of a
  Projective Garbled Scheme and an Oblivious Transfer protocol.

   Party 2 inputs:  - the circuit (function "f") to be evaluated
                    - the inputs for (possibly empty) subset of input wires ("i2")
   Party 2 output: (none)
   Party 1 input:   - inputs for the remaining input wires ("i1")
   Party 1 output:  - evaluated output ("f(i1||i2)")
 
  The distinction between SFE/PFE is given only by the adopted notion of
  "circuit leakage": in PFE, Party 2 leaks the same notion of leakage adopted
  by the underlying garbled scheme (i.e., the topology of the circuit). In SFE,
  all the circuit is leaked, turning the evaluated function publicly available.
  Besides the circuit leakage, Party 2 also leaks the number of input wires that
  he fills in. In either case, Party 1 leaks the size of his inputs.
*)
theory SFE.

  (** Projective garbling scheme *)
  clone import ProjSch.ProjScheme.

  (** Instantiation of the security definitions for garbling schemes
    with the projective scheme above *)
  clone SchSec.SchSecurity with
    theory Sch.Scheme <- ProjScheme.Sch.Scheme.

  (** Oblivious transfer protocol *)
  (**
    Since we are dealing with a projective garbling scheme defined over
    bit strings and tokens, we need the oblivious transfer protocol defined
    over those types too.
      
    The oblivous transfer protocol must allow the transmission of a token array
    (that represents the garbled input) without the sender knowing the token
    array sent and without the receiver knowing anything about the encoding 
    function.

    The sender will input to the protocol the encoding key that is composed
    of an array of doubles of tokens and the receiver will input to the 
    protocol the decision bit string (its input).
  *)
  (** OT protocol parameters *)
  type ot_rand1_t.
  type ot_rand2_t.
  type ot_conv_t.
  op ot_prot: bool array -> ot_rand1_t ->
              (token_t * token_t) array ->
              ot_rand2_t -> ot_conv_t * (token_t array * unit).

  (** Instantiation of the OT protocol and of its security definitions *)
  clone OTSec.OTSecurity with
    type OT.msg_t = token_t,
    type OT.rand1_t = ot_rand1_t,
    type OT.rand2_t = ot_rand2_t,
    type OT.conv_t = ot_conv_t,
    op OT.prot = ot_prot.

  (** These definitions establish sufficient conditions to
     glue a Scheme to an OT *)

  (** 
    SFE/PFE leakage:

    Depending if we are interested in a "Private Function Evaluation" (PFE),
    or a "Secure Function Evaluation" (SFE) scenario, we will consider different
    notions of leakage for Party 2. 
  *)
  op sfe_sch_phi: Sch.Scheme.fun_t -> Sch.Scheme.fun_t.

  (**
    We impose however that the adopted notion of leakage allow us to obtain:
      - OT's public data;
      - the circuit topology (scheme's leaked data)
  *)
  op leakInterface: Sch.Scheme.fun_t * int -> Sch.Scheme.leak_t * int.


  (** Instantiation of a SFE protocol as a two-party secure protocol *)
  (** 
    The protocol is instantiated as follows: 
      - P1 randomness -> OT random
      - P1 input -> boolean array (bit string or wires to the circuit being
      evaluated). 
      - P1 output -> output of the boolean circuit
      - P1 leakage -> length of its input
      - P2 randomness -> OT random and garbling scheme random
      - P2 input -> function to be evaluated and its input
      - P2 output -> nothing
      - P2 leakage -> all the scheme (SFE not PFE) and length of its input
      - Functionallity of the circuit (ev_1,ev_2) -> evaluation of the function
      with both inputs for party P1 and nothing for party P2
      - Views -> the garbled scheme, garbled input and decoding key for party P1
      and messages exchanged in the OT protocol for party P2.
      - Validity of the inputs -> since it is going to be part of the OT protocol, the
      size of I1 must be admissible for the OT protocol and both inputs need to be
      valid according to the function to be evaluated
      - Validity of the randomness -> valid randomness for the garbling scheme
      - Leakage of party P1 -> length of selection bit string (input)
      - Leakage of party P2 -> all the circuit and length of its input
      - Protocol -> execution that results in the evaluation of the function by
      party P1 and nothing for party P2
  *)
  clone ProtSec.ProtSecurity with
    type Protocol.rand1_t = OTSecurity.OTPSec.Protocol.rand1_t,
    type Protocol.input1_t = bool array,
    type Protocol.output1_t = Sch.Scheme.output_t,
    type Protocol.leak1_t = int,
    type Protocol.rand2_t = OTSecurity.OTPSec.Protocol.rand2_t * Sch.Scheme.rand_t,
    type Protocol.input2_t = Sch.Scheme.fun_t * (bool array),
    type Protocol.output2_t = unit,
    type Protocol.leak2_t = Sch.Scheme.fun_t * int,
    op Protocol.f (i1: input1_t, i2: input2_t) = (Sch.Scheme.eval (fst i2) (i1 || snd i2), ()),
    type Protocol.conv_t = (Sch.Scheme.funG_t * token_t array * Sch.Scheme.outputK_t) *
                  OTSecurity.OTPSec.Protocol.conv_t,

    op Protocol.validInputs(i1: input1_t, i2: input2_t) =
     0 < size i1 <= OTSecurity.OT.max_size /\ Sch.Scheme.validInputs (fst i2) (i1||snd i2),

    pred Protocol.validRands(i1: input1_t, i2: input2_t, r1: rand1_t, r2: rand2_t) = Sch.Scheme.validRand (fst i2) (snd r2),

    op Protocol.phi1 = OTSecurity.OTPSec.Protocol.phi1,

    op Protocol.phi2(i2:input2_t) = (sfe_sch_phi (fst i2), size (snd i2)),

    op Protocol.prot(i1: bool array, r1: OTSecurity.OTPSec.Protocol.rand1_t, 
          i2:Sch.Scheme.fun_t * bool array, r2: OTSecurity.OTPSec.Protocol.rand2_t*Sch.Scheme.rand_t) =
      let fG = Sch.Scheme.funG (fst i2) (snd r2) in
      let oK = Sch.Scheme.outputK (fst i2) (snd r2) in
      let iK = Sch.Scheme.inputK (fst i2) (snd r2) in
      let (ot_conv, ot_res) = OTSecurity.OTPSec.Protocol.prot i1 r1 (take (snd (leakInterface (sfe_sch_phi (fst i2), size (snd i2)))) iK) (fst r2) in
      let i2G = Sch.Scheme.Input.encode (drop (size i1) iK) (snd i2) in
                (((fG,i2G,oK),ot_conv) (* conversation *)
                 ,(Sch.Scheme.decode oK (Sch.Scheme.evalG fG (fst ot_res || i2G)),() (* results *) )).

  import ProtSecurity.
  import Protocol.

  (*********************)
  (* Correctness proof *)
  (*********************)

  (** Compatibility predicate *)
  (** 
    The compatibility predicate states that the leakage of the protocol is
    equal to the leakage of the garbling scheme, the size of the inputs is the same
    and that the size of the encoding key is the size of |i1| + |i2|.
  *)
  pred Compatibility (x:unit) = forall i1 i2,
    validInputs i1 i2 =>
    fst (leakInterface (phi2 i2)) = Sch.Scheme.phi (fst i2) /\
    snd (leakInterface (phi2 i2)) = size i1 /\
    forall r,
      size (Sch.Scheme.inputK (fst i2) r) = size i1 + size (snd i2).

  (** If the protocol is compatible, then the leakage of the protocol is
    equal to the leakage of the garbling scheme *)
  lemma compat_leak1 i1 i2:
    Compatibility () =>
    validInputs i1 i2 =>
    fst (leakInterface (phi2 i2)) = Sch.Scheme.phi (fst i2) by [].

  (** If the protocol is compatible, then the size of inputs is the same *)
  lemma compat_leak2 i1 i2:
    Compatibility () =>
    validInputs i1 i2 =>
    snd (leakInterface (phi2 i2)) = size i1 by [].

  (** If the protocol is compatible, then the inputs are valid to the OT protocol *)
  lemma PFE_validInputs_OT i1 i2 r:
    Compatibility () =>
    validInputs i1 i2 =>
    OTSecurity.OTPSec.Protocol.validInputs i1 (take (size i1) (Sch.Scheme.inputK (fst i2) r)) by [].

  (** If the inputs are not valid for the protocol, they are not valid to the OT protocol *)
  lemma PFE_validInputs_OT_n i1 i2 r:
    !validInputs i1 i2 =>
    !OTSecurity.OTPSec.Protocol.validInputs
       i1 
       (if validInputs i1 i2
        then (take (size i1) (Sch.Scheme.inputK (fst i2) r) )
        else empty%Array) by [].

  (** Correctness of the protocol: ((ev_1(I_1, I_2), ev_2(I_1, I_2)) = 
     (\Pi_1(I_1), \Pi_2(I_2))) *)
  lemma PFE_Correctness:
    Compatibility () =>
    ProjScheme.Sch.Scheme.Correct() =>
    OTSecurity.OTPSec.Correct () =>
    Correct (). 
  proof. 
    rewrite /ProjScheme.Sch.Scheme.Correct /OTSecurity.OTPSec.Correct /Correct /validRands.
    move=> compat schcorr otcorr i1 r1 i2 r2 validInputs validRands.
    rewrite /prot -/OTSecurity.OT.prot -/OTSecurity.OTPSec.Protocol.prot=> //=.
    pose otprot:= OTSecurity.OTPSec.Protocol.prot _ _ _ _.
    rewrite (pairS otprot) /=.
    rewrite /otprot -otcorr=> // {otprot otcorr}.
      cut ->: snd (leakInterface (sfe_sch_phi (fst i2), size (snd i2))) =
             size i1 by (by apply (compat_leak2 i1 i2 _ _)) => //.
      by apply PFE_validInputs_OT => //.
    rewrite /f /OTSecurity.OTPSec.Protocol.f snd_pair fst_pair.
    cut ->: snd (leakInterface (sfe_sch_phi (fst i2), size (snd i2))) =
           size i1 by (by apply (compat_leak2 i1 i2 _ _)).
    rewrite (schcorr (snd r2) (fst i2) (i1||snd i2)); first 2 smt.
    pose fG := (Sch.Scheme.funG (fst i2) (snd r2)).
    pose iK := (Sch.Scheme.inputK (fst i2) (snd r2)).
    pose oK := (Sch.Scheme.outputK (fst i2) (snd r2)).
    simplify; cut:= compat i1 i2.
    simplify Compatibility validInputs=> {compat} compat.
    rewrite size_take; first smt.
    cut ->: offun (fun (k : int),
              if i1.[k] then snd (take (size i1) iK).[k]
              else fst (take (size i1) iK).[k]) (size i1)
            = Sch.Scheme.Input.encode (take (size i1) iK) i1.
      rewrite /Sch.Scheme.Input.encode; congr; expect 2 by smt. 
      pose iG := (Sch.Scheme.Input.encode  iK (i1 || snd i2)).
    rewrite /oK.
    congr => //.
    rewrite /iG /fG.
    by rewrite encode_take_drop; smt.
  qed. 

  (** Random generators *)
  (** 
    Random generators generate randomness according to leakage information.
  *)
  module PFE_R1(OT_R1:OTSecurity.OTPSec.Rand1_t): Rand1_t = {
    proc gen(i1info: leak1_t): rand1_t = {
      var r: rand1_t;

      r = OT_R1.gen(i1info);
      return r;
    }
  }.

  module PFE_R2(OT_R2:OTSecurity.OTPSec.Rand2_t,G_R:SchSecurity.EncSecurity.Rand_t) : Rand2_t = {
    proc gen(i2info : leak2_t) : rand2_t = {
      var r1 : OTSecurity.OTPSec.Protocol.rand2_t;
      var r2 : Sch.Scheme.rand_t;

      r1 = OT_R2.gen(snd (leakInterface i2info));
      r2 = G_R.gen(fst (leakInterface (i2info)));
      return (r1,r2);
    }
  }.

  (** Simulator *)
  (**
     A simulator is defined for both parties.

     A simulator must simulate the execution of a two-party protocol for a party, with 
     respect to the input of that party, the expected output and the leakage of the
     input of the other party. The output of the simulator is an execution of the protocol (a view)
     that would produce the expeted output of the party given its input and with information
     of the input of the other party.

     The simulator of the protocol makes use of the random generator of the garbling scheme,
     the simulator of the garbling scheme and of the simulator of the OT protocol.

     For party P1, the simulator takes the leakage of the garbling scheme to produce a
     simulated garbled circuit, a simulated garbled input and simulated decoding key. Then
     it simulates the execution of the OT protocol and outputs the messages exchanged in the 
     OT protocol as well as the simulated garbling scheme values.

     For party P2, the simulator simulates the execution of the OT protocol and outputs the
     view of party P2 in the OT protocol together with a truly garbling scheme values.
  *)
  module PFE_S (G_R:SchSecurity.EncSecurity.Rand_t,
                G_S:SchSecurity.EncSecurity.Sim_SIM_t,
                OT_S:OTSecurity.OTPSec.Sim_t): Sim_t = {
    proc sim1(i1: input1_t, o1: output1_t, l2 : leak2_t): view1_t = {
      var fG: Sch.Scheme.funG_t;
      var xG: ProjScheme.token_t array;
      var oK: Sch.Scheme.outputK_t;
      var ot_t: OTSecurity.OTPSec.Protocol.conv_t;
      var ot_r1: OTSecurity.OTPSec.Protocol.rand1_t;
      var sch_leakage: SchSecurity.EncSecurity.Encryption.leakage;

      sch_leakage =  (fst (leakInterface l2),o1);
      (fG, xG, oK) = G_S.simm(sch_leakage); 
      (ot_r1,ot_t) = OT_S.sim1(i1, take (size i1) xG, snd (leakInterface l2));
      return (ot_r1, ((fG, drop (snd (leakInterface l2)) xG, oK), ot_t));
    }

    proc sim2(i2: input2_t, o2: output2_t, l1: leak1_t): view2_t = {
      var g_r : Sch.Scheme.rand_t;
      var ot_t : OTSecurity.OTPSec.Protocol.conv_t;
      var ot_r2 : OTSecurity.OTPSec.Protocol.rand2_t;

      g_r = G_R.gen (Sch.Scheme.phi (fst i2));
      (ot_r2, ot_t) = OT_S.sim2(take l1 (Sch.Scheme.inputK (fst i2) g_r), o2, l1);   
      return ((ot_r2,g_r),((Sch.Scheme.funG (fst i2) g_r
                           ,Sch.Scheme.Input.encode (drop l1 (Sch.Scheme.inputK (fst i2) g_r)) (snd i2) 
             ,Sch.Scheme.outputK (fst i2) g_r), ot_t));
    }
  }.
  
  (***************************)
  (* Lossnessness properties *)
  (***************************)
  
  lemma PFE_R1_ll (OT_R1 <: OTSecurity.OTPSec.Rand1_t):
    islossless OT_R1.gen =>
    islossless PFE_R1(OT_R1).gen.
  proof.
    by move=> OT_R1genL;
    proc; call OT_R1genL.
  qed.

  lemma PFE_R2_ll (OT_R2 <: OTSecurity.OTPSec.Rand2_t) (G_R <: SchSecurity.EncSecurity.Rand_t):
    islossless OT_R2.gen =>
    islossless G_R.gen =>
    islossless PFE_R2(OT_R2,G_R).gen.
  proof.
    by move=> OT_R2genL G_RgenL;
    proc; call G_RgenL; call OT_R2genL.
  qed.

  lemma PFE_Ssim1_ll (G_R <: SchSecurity.EncSecurity.Rand_t)
                     (G_S <: SchSecurity.EncSecurity.Sim_SIM_t)
                     (OT_S <: OTSecurity.OTPSec.Sim_t):
    islossless G_S.simm =>
    islossless OT_S.sim1 =>
    islossless PFE_S(G_R,G_S,OT_S).sim1.
  proof.
    by move=> G_SsimL OT_Ssim1L;
    proc; call OT_Ssim1L; call G_SsimL; wp.
  qed.

  lemma PFE_Ssim2_ll (G_R <: SchSecurity.EncSecurity.Rand_t)
                     (G_S <: SchSecurity.EncSecurity.Sim_SIM_t)
                     (OT_S <: OTSecurity.OTPSec.Sim_t):
    islossless G_R.gen =>
    islossless OT_S.sim2 =>
    islossless PFE_S(G_R,G_S,OT_S).sim2.
  proof.
    by move=> G_RgenL OT_Ssim2L;
    proc; call OT_Ssim2L; call G_RgenL.
  qed.


  (*********************)
  (* Security proof    *)
  (*********************)

  (**
    The construction of the SFE/PFE protocol is made by a modular
    combination of an arbitrary garbling scheme and an arbitrary OT protocol.
    This reduces the security of the protocol to the security of its
    two constituents. Therefore, informally, what we need to prove is that
    the garbling scheme is SIM secure over some leakage function and that
    the OT protocol is PFE-SIM secure over some other leakage function.
  *)

  section.

    (**************************)
    (* Adversaries definition *)
    (**************************)
  
    (** Adversary attacking OT Game1 *)
    (**
      This adversary will run another adversary already defined in the 
      security notions of a protocol. 

      In order to generate its query, the adversary will make use of the
      adversary attacking the protocol to produce its own query. It will
      invoke the protocol adversary to obtain its query and then produce 
      its query made of one input (boolean array) and of a encoding key.

      This adversary will also ask the protocol adversary to distinguish
      between its view (protocol view) or a view of the execution of the
      OT protocol. The intuition the OT protocol reveals no additional
      information from the one revealed by the SFE/PFE protocol.
    *)
    module B_OT1(G_R: SchSecurity.EncSecurity.Rand_t,
                 A1: Adv1_t): OTSecurity.OTPSec.Adv1_t = {
      var fG : Sch.Scheme.funG_t
      var iG : ProjScheme.token_t array
      var oK : Sch.Scheme.outputK_t

      proc gen_query(): bool array * (ProjScheme.token_t * ProjScheme.token_t) array = {
        var x1 : bool array;
        var fn : Sch.Scheme.fun_t;
        var i2 : Sch.Scheme.fun_t * bool array;
        var x2 : bool array;
        var iK : (ProjScheme.token_t * ProjScheme.token_t) array;
        var r : Sch.Scheme.rand_t;

        (x1,i2) = A1.gen_query();
        (fn,x2) = i2;
        
        r = G_R.gen (Sch.Scheme.phi fn);
        fG = Sch.Scheme.funG fn r;
        iK = Sch.Scheme.inputK fn r;
        iG = Sch.Scheme.Input.encode (drop (size x1) iK) x2;
        oK = Sch.Scheme.outputK fn r;
        return (x1, if validInputs x1 i2
                    then (take (size x1) (Sch.Scheme.inputK fn r))
                    else empty%Array);
      }

      proc dist(view: OTSecurity.OTPSec.view1_t): bool = {
        var guess : bool;

        guess = A1.dist(fst view,((fG, iG, oK), snd view));
        return guess;
      }
    }.

    (** Adversary attacking the garbling scheme *)
    (**
      This adversary will run another adversary already defined in the 
      security notions of a protocol. 

      In order to generate its query, the adversary will make use of the
      adversary attacking the protocol to produce its own query. It will
      invoke the protocol adversary to obtain its query and then produce 
      its query made of the function to be evaluated and of the input
      to the function (concatenation of both inputs).

      The adversary will then generated its challenge by obtaining from the
      Garble oracle (F,X,d) (called with the query generated) and then
      by simulating the execution of an OT protocol with a forged encoding key
      for P2. 

      This adversary will finally ask the protocol adversary to distinguish
      between its view (protocol view) or a view of the execution of the
      OT protocol. The intuition here is that the OT protocol reveals no additional
      information from the one revealed by the SFE/PFE protocol.
    *)
    module B_G(OT_S: OTSecurity.OTPSec.Sim_t,
               A1: Adv1_t): SchSecurity.EncSecurity.Adv_SIM_t = {
      var x1 : bool array
      var fn : Sch.Scheme.fun_t
      var x2 : bool array

      proc gen_query(): SchSecurity.EncSecurity.query_SIM = {
          var i2 : Sch.Scheme.fun_t * bool array;
          (x1,i2) = A1.gen_query();
          (fn,x2) = i2;

          return (fn,x1 || x2);
      }

      proc get_challenge(cipher:SchSecurity.EncSecurity.Encryption.cipher) : bool = {
        var fG : Sch.Scheme.funG_t;
        var xG : ProjScheme.token_t array;
        var oK : Sch.Scheme.outputK_t;
        var ot_r1 : OTSecurity.OT.rand1_t;
        var ot_t : OTSecurity.OT.conv_t;
        var guess : bool;

        if (0 < size x1 <= OTSecurity.OT.max_size) {
          (fG,xG,oK) = cipher;
          (ot_r1,ot_t) = OT_S.sim1(x1, take (size x1) xG,
                                   snd (leakInterface (phi2 (fn,x2))));
          guess = A1.dist((ot_r1, ((fG, drop (size x1) xG, oK), ot_t))); 
        } else {
          guess = ${0,1};
        }
        return guess;
      }
    }.

    (** Adversary attacking OT Game2 *)
    (**
      This adversary is defined form party P2. Since party P2
      obtains nothing from party P1 other than what it gets from the 
      execution of the OT protocol, the security follows directly from the
      assumption that the OT protocol is secure.

      The game that captures this property is, thus, similar to the
      previous OT game. The only difference relies on the query,
      since P2 can see random coins from the OT protocol and from 
      the garbling scheme.
    *)
    module B_OT2(G_R: SchSecurity.EncSecurity.Rand_t,
                 A2: Adv2_t): OTSecurity.OTPSec.Adv2_t = {
      var fG: Sch.Scheme.funG_t
      var oK: Sch.Scheme.outputK_t
      var iG: ProjScheme.token_t array
      var r : Sch.Scheme.rand_t

      proc gen_query(): OTSecurity.OTPSec.Protocol.input1_t * OTSecurity.OTPSec.Protocol.input2_t  = {
          var x1 : bool array;
          var x2 : bool array;
          var fn : Sch.Scheme.fun_t;
          var iK : (ProjScheme.token_t * ProjScheme.token_t) array;
          var i2 : Sch.Scheme.fun_t * bool array;

          (x1,i2) = A2.gen_query();
          (fn,x2) = i2;

          r = G_R.gen (Sch.Scheme.phi fn);
          fG = Sch.Scheme.funG fn r;
          iK = Sch.Scheme.inputK fn r;
          iG = Sch.Scheme.Input.encode (drop (size x1) iK) x2;
          oK = Sch.Scheme.outputK fn r;
          return (x1, if validInputs x1 i2
                      then take (size x1) (Sch.Scheme.inputK fn r)
                      else empty%Array);
      }

      proc dist(view: OTSecurity.OTPSec.view2_t) : bool = {
        var guess : bool;

        guess = A2.dist(((fst view, r), ((fG, iG, oK), snd view)));
        return guess;
      }
    }.

    (***************************)
    (* Lossnessness properties *)
    (***************************)
    
    lemma B_OT1_gen_ll (G_R<: SchSecurity.EncSecurity.Rand_t) (A1<: Adv1_t):
      islossless G_R.gen =>
      islossless A1.gen_query =>
      islossless B_OT1(G_R,A1).gen_query.
    proof. by move=> G_RgenL A1genL; proc; wp; call G_RgenL; wp; call A1genL. qed.

    lemma B_OT1_dist_ll (G_R<: SchSecurity.EncSecurity.Rand_t) ( A1<: Adv1_t):
      islossless A1.dist =>
      islossless B_OT1(G_R,A1).dist.
    proof. by move=> A1distL; proc; wp; call A1distL. qed.

    lemma B_G_gen_ll (OT_S <: OTSecurity.OTPSec.Sim_t) (A1 <: Adv1_t):
      islossless A1.gen_query =>
      islossless B_G(OT_S,A1).gen_query.
    proof. by move=> A1genL; proc; wp; call A1genL. qed.

    lemma B_G_dist_ll (OT_S <: OTSecurity.OTPSec.Sim_t) (A1 <: Adv1_t):
      islossless OT_S.sim1 =>
      islossless A1.dist =>
      islossless B_G(OT_S,A1).get_challenge.
    proof.
     move=> OT_Ssim1L A1distL; proc; case (0 < size B_G.x1 <= OTSecurity.OT.max_size).
      rcondt 1; first by skip.
      by call A1distL; call OT_Ssim1L; wp.
     rcondf 1; first by skip.
     by rnd; skip; smt.
    qed.

    lemma B_OT2_gen_ll (G_R <: SchSecurity.EncSecurity.Rand_t) (A2 <: Adv2_t):
      islossless G_R.gen =>
      islossless A2.gen_query =>
      islossless B_OT2(G_R,A2).gen_query.
    proof. by move=> G_RgenL A2genL; proc; wp; call G_RgenL; wp; call A2genL. qed.

    lemma B_OT2_dist_ll (G_R <: SchSecurity.EncSecurity.Rand_t) (A2 <: Adv2_t):
      islossless A2.dist =>
      islossless B_OT2(G_R,A2).dist.
    proof. by move=> A2distL; proc; call A2distL. qed.

    (**********************************)
    (*       Party 1 simulation       *)
    (**********************************) 
    (**
      The party P1 security game of a two-party protocol must be 
      indistinguishable from the OT security game instantiated
      with the adversaries defined above.
      
      Recall that we are comparing views and the security intuition tells us that
      the views should be indistinguishable from one another. 
    *)
    local lemma Game1_real_equiv (A1<:Adv1_t {B_OT1})
                                 (OT_S<:OTSecurity.OTPSec.Sim_t)
                                 (G_S<:SchSecurity.EncSecurity.Sim_SIM_t)
                                 (OT_R1<:OTSecurity.OTPSec.Rand1_t {A1,B_OT1})
                                 (OT_R2<:OTSecurity.OTPSec.Rand2_t {A1,B_OT1,OT_R1}) 
                                 (G_R<:SchSecurity.EncSecurity.Rand_t {A1,OT_R1,OT_R2}):
      islossless OT_S.sim1 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.dist =>
      Compatibility () =>
      equiv [ OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).game ~ 
              Game1(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A1).game:
                ={glob OT_R1,glob OT_R2,glob A1,glob G_R,b} /\ b{1} ==> ={res} ].
    proof.
      move=> OT_Ssim1L G_RgenL G_SsimL A1distL compat.
      proc => //.
      inline B_OT1(G_R,A1).gen_query.
      seq 2 1: (x1{1} = i1{2} /\ i20{1} = i2{2} /\ fn{1} = fst i20{1} /\
              x2{1} = snd i20{1} /\ b{1} /\ b{2} /\
              ={glob A1, glob G_R,glob OT_R1,glob OT_R2}).
        by wp; call (_: true); auto.
      case (validInputs i1{2} i2{2}); last first.
      rcondt{2} 1=> //; rcondt{1} 7;
        first by move => &m; wp; call (_: true); wp; skip; smt.
        by rnd; wp; call{1} G_RgenL; wp; skip; progress; smt.
      (* validInputs i1 i2 *)
      rcondf{2} 1=> //.
      inline PFE_R1(OT_R1).gen PFE_R2(OT_R2,G_R).gen B_OT1(G_R, A1).dist.
      rcondt{2} 1=> //.
      rcondf{1} 7.
      move => &m; wp; call (_ : true); skip.
      cut HH: (forall i1 i2 r, Compatibility () =>
                    Protocol.validInputs i1 i2 =>
                    OTSecurity.OTPSec.Protocol.validInputs i1 (take (size i1) (Sch.Scheme.inputK (fst i2) r)))
        by apply PFE_validInputs_OT.
        by smt.
      rcondt{1} 7.
        by move => &m; wp; call (_:true); skip; progress; smt.
      wp; call (_: true).
      wp.
      swap{2} 6 -1; swap {2} [4..5] -3.
      wp; call (_: true).
      wp; call (_: true).
      wp; call (_: true).
      wp; skip; progress.
        by rewrite -(compat_leak1 i1{2}).
        by rewrite H1 /=; smt.
        by rewrite H1 /= /prot; smt.
        by smt.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game1_real_pr (A1<:Adv1_t {B_OT1})
                              (OT_S<:OTSecurity.OTPSec.Sim_t)
                              (G_S<:SchSecurity.EncSecurity.Sim_SIM_t)
                              (OT_R1<:OTSecurity.OTPSec.Rand1_t {A1,B_OT1})
                              (OT_R2<:OTSecurity.OTPSec.Rand2_t {A1,B_OT1,OT_R1}) 
                              (G_R<:SchSecurity.EncSecurity.Rand_t {A1,OT_R1,OT_R2})
                              &m:
      islossless OT_S.sim1 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.dist =>
      Compatibility () =>
      Pr[ OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).game(true)
          @ &m : res ] =
      Pr[ Game1(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A1).game(true)
          @ &m : res ].
    proof.
      by move=> OT_Ssim1L G_RgenL G_SsimL A1distL compat;
      byequiv (Game1_real_equiv A1 OT_S G_S OT_R1 OT_R2 G_R _ _ _ _ _)=> //; smt.
    qed.

    (**
      The security game for an OT protocol instantiated with the adversaries
      above should be indistinguishable from the security game for the garbling
      scheme instantiated with the adversaries above. Informally, this means 
      that the OT protocol and the garbling scheme release the same information
      about the protocol.
    *)
    local lemma Game1_hybrid_equiv (A1 <: Adv1_t {B_OT1,B_G})
                                   (OT_S <: OTSecurity.OTPSec.Sim_t {A1,B_OT1,B_G})
                                   (G_S <: SchSecurity.EncSecurity.Sim_SIM_t)
                                   (OT_R1<: OTSecurity.OTPSec.Rand1_t {A1,B_G})
                                   (OT_R2<: OTSecurity.OTPSec.Rand2_t {A1,OT_R1,B_G}) 
                                   (G_R<: SchSecurity.EncSecurity.Rand_t {A1,B_G,B_OT1,OT_S}):
      islossless OT_R1.gen =>
      islossless OT_R2.gen =>
      islossless OT_S.sim1 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.dist =>
      Compatibility () =>
      OTSecurity.OTPSec.Correct () =>
      equiv [OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).game ~
            SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).game:
              ={glob OT_R1,glob OT_R2,glob A1,glob G_R,glob OT_S} /\ !b{1} /\ b{2} ==> res{1}=!res{2} ].
    proof.
      move => OT_R1genL OT_R2genL OT_Ssim1L G_RgenL G_SsimL A1distL compat OTcorrect; proc.
      inline B_OT1(G_R,A1).gen_query B_OT1(G_R,A1).dist.
      inline B_G(OT_S,A1).gen_query B_G(OT_S,A1).get_challenge.
      seq 2 2: (x1{1} = B_G.x1{2} /\ i20{1} = i2{2} /\ fn{1} = B_G.fn{2} /\
              x2{1} = B_G.x2{2} /\ (B_G.fn{2}, B_G.x2{2}) = i2{2} /\
              (fn{1}, x2{1}) = i20{1} /\ ={glob OT_R1,glob OT_R2,glob OT_S, glob A1, glob G_R} /\ !b{1} /\ b{2}).
        by wp;call (_: true); skip; progress; smt.
      case (validInputs x1{1} (fn{1},x2{1})); last first.
      (* Suppose invalid protocol inputs *)
        rcondt{1} 7. 
          move => &m; wp; call (_ : true).
          by skip; progress; smt.
        case (!(SchSecurity.EncSecurity.queryValid_SIM (B_G.fn{2}, B_G.x1{2} || B_G.x2{2}))).
          rcondt {2} 2; first by move => &m; wp; skip; smt.
          rnd; wp; call {1} G_RgenL.
          by skip; progress; smt.
        rcondf {2} 2; first move => &m; wp; skip; smt.
        rcondt {2} 2; first by move => &m; wp; skip; trivial.
        rcondf {2} 5; first move => &m; wp. 
          call (_ : true).
          by wp; skip; progress; smt.
        wp; rnd; wp.
        call (_: true).
        by wp; skip; progress; smt.
      (* protocol validInputs *)
        rcondf {2} 2; first by move => &m; wp; skip; smt.
        rcondt {2} 2; first by move => &m; wp; skip; smt.
        rcondt {2} 5; first move => &m; wp. 
          call (_ : true).
          by wp; skip; smt.
        rcondf{1} 7.
          by move => &m; wp; call (_: true); skip; smt.
        rcondf{1} 7.
          by move => &m; wp; call (_: true); skip; smt.
        wp; call (_: true).
        wp; call (_: true).
        wp; call (_: true).
        wp; skip; progress => //;
      rewrite ?H5 /=; move : H6;
      rewrite /SchSecurity.EncSecurity.Encryption.enc
              /OTSecurity.OTPSec.Protocol.f; progress.
      do !rewrite /fst /snd=> /=.
      rewrite !size_take; first by split; smt.
      rewrite -encode_take; first smt.
      rewrite /Sch.Scheme.Input.encode.
      rewrite !size_take; first by split; smt.
      by congr; apply fun_ext=> k; case (B_G.x1{2}.[k]); smt.
      rewrite (compat_leak2 B_G.x1{2} (B_G.fn{2},B_G.x2{2})) //.
      delta=> //=; smt. 
        cut [_] [_] len_r:= compat B_G.x1{2} (B_G.fn,B_G.x2){2} _=> //.
      by rewrite fst_pair snd_pair encode_drop; smt.
      by smt.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game1_hybrid_pr (A1<: Adv1_t {B_OT1,B_G})
                                (OT_S<: OTSecurity.OTPSec.Sim_t {A1,B_OT1,B_G})
                                (G_S<: SchSecurity.EncSecurity.Sim_SIM_t)
                                (OT_R1<: OTSecurity.OTPSec.Rand1_t {A1,B_G})
                                (OT_R2<: OTSecurity.OTPSec.Rand2_t {A1,OT_R1,B_G}) 
                                (G_R<: SchSecurity.EncSecurity.Rand_t {A1,B_G,OT_S,B_OT1})
                                &m:
      islossless OT_R1.gen =>
      islossless OT_R2.gen =>
      islossless OT_S.sim1 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.dist =>
      Compatibility () =>
      OTSecurity.OTPSec.Correct () =>
      Pr [OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).game(false) @ &m: !res] =
      Pr [SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).game(true) @ &m: res].
    proof.
      by move => OT_R1genL OT_R2genL OT_SsimL G_RgenL G_SsimL A1distL compat OTcorrect;
      byequiv (Game1_hybrid_equiv A1 OT_S G_S OT_R1 OT_R2 G_R _ _ _ _ _ _ _ _).
    qed.

    (**
      The security game of a two-party protocol must be indistinguishable from the
      garbling scheme game instantiated with the adversaries defined above. Informally,
      this means that the execution of the garbling scheme reveals no additional 
      information other that the one revealed by the protocol.
    *)
    local lemma Game1_ideal_equiv (A1 <: Adv1_t {B_OT1,B_G})
                                  (OT_S <: OTSecurity.OTPSec.Sim_t {A1,B_OT1,B_G})
                                  (G_S <: SchSecurity.EncSecurity.Sim_SIM_t {A1,B_G,OT_S})
                                  (OT_R1 <: OTSecurity.OTPSec.Rand1_t {A1,B_G})
                                  (OT_R2 <: OTSecurity.OTPSec.Rand2_t {A1,OT_R1,B_G})
                                  (G_R <: SchSecurity.EncSecurity.Rand_t {A1,B_G}):
      islossless OT_R1.gen =>
      islossless OT_R2.gen =>
      islossless OT_S.sim1 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.dist =>
      Compatibility () =>
      OTSecurity.OTPSec.Correct () =>
      equiv [Game1(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A1).game ~
            SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).game:
              ={glob OT_R1,glob OT_R2,glob A1,glob G_R,glob OT_S,glob G_S} /\ !b{1} /\ !b{2} ==> ={res} ].
    proof.
      move => OT_R1genL OT_R2genL OT_Ssim1L G_RgenL G_SsimL A1distL compat OTcorrect; proc.
      inline PFE_R1(OT_R1).gen PFE_R2(OT_R2,G_R).gen PFE_S(G_R,G_S,OT_S).sim1.
      inline B_G(OT_S,A1).gen_query B_G(OT_S,A1).get_challenge.
      seq 1 2: (i1{1} = B_G.x1{2} /\ i2{1} = i2{2} /\ (fst i2{2} = B_G.fn{2}) /\
               snd i2{2} = B_G.x2{2} /\ !b{1} /\ !b{2} /\ ={glob OT_R1,glob OT_R2,glob OT_S,glob A1,glob G_R,glob G_S}).
        by wp; call (_: true).
      case (validInputs i1{1} i2{1}); last first.
      rcondt{1} 1=> //.
      case (! (SchSecurity.EncSecurity.queryValid_SIM (B_G.fn{2}, B_G.x1{2} || B_G.x2{2}))).
        rcondt{2} 2; first move => &m; wp; skip; smt.
        by rnd; wp; skip; smt.
      rcondf{2} 2; first move => &m; wp; skip; smt.
      rcondf{2} 2; first by move => &m; wp; skip; smt.
      rcondf{2} 4.
        move => &m; wp.
        call (_ : true)=> //.
        by wp; skip; smt.
      wp; rnd; wp; call{2} G_SsimL; wp.
        by skip; smt.
      (* validInputs *)
      rcondf{1} 1=> //.
      rcondf{2} 2; first by move => &m; wp;skip; smt.
      rcondf{1} 1=> //; rcondf{2} 2; first by move => &m; wp.
      rcondt{2} 4.
        move => &m; wp.
        call (_ : true)=> //; first by wp; skip; smt.
      wp; call (_: true).
      wp; call (_: true).
      wp; call (_: true).
      wp; skip; progress => //.
        by rewrite (compat_leak1 B_G.x1{2}).
        by rewrite (compat_leak2 B_G.x1{2}).
        by smt.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game1_ideal_pr (A1<: Adv1_t {B_OT1,B_G})
                               (OT_S<: OTSecurity.OTPSec.Sim_t {A1,B_OT1,B_G})
                               (G_S<: SchSecurity.EncSecurity.Sim_SIM_t {A1,B_G,OT_S})
                               (OT_R1<: OTSecurity.OTPSec.Rand1_t {A1,B_G})
                               (OT_R2<: OTSecurity.OTPSec.Rand2_t {A1,OT_R1,B_G})
                               (G_R<: SchSecurity.EncSecurity.Rand_t {A1,B_G})
                               &m:
      islossless OT_R1.gen =>
      islossless OT_R2.gen =>
      islossless OT_S.sim1 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.dist =>
      Compatibility () =>
      OTSecurity.OTPSec.Correct () =>
      Pr [Game1(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A1).game(false)
         @ &m: !res] =
      Pr [SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).game(false)
         @ &m: !res].
    proof.
      by move => OT_R1genL OT_R2genL OT_Ssim1L G_RgenL G_SsimL A1distL compat OTcorrect;
      byequiv (Game1_ideal_equiv A1 OT_S G_S OT_R1 OT_R2 G_R _ _ _ _ _ _ _ _).
    qed.

    (**********************************)
    (*       Party 2 simulation       *)
    (**********************************)
    (**
      For party two it's easy: we are only concerned with the security of the OT
      protocol since P2 will not obtain any information about belongings of P1.

      The equality above states that the OT security game instantiated with the
      adversaries defined above must be indistinguishable from the protocol security
      game defined for party P2. Informally, this means that party P2 learns nothing
      more than admissible from the SFE/PFE protocol with the execution of the 
      execution of the OT protocol.
    *)
    local lemma Reduction2 (A2<: Adv2_t {B_OT2,B_G})
                           (OT_S<: OTSecurity.OTPSec.Sim_t {A2,B_OT2,B_G})
                           (G_S<: SchSecurity.EncSecurity.Sim_SIM_t {A2,OT_S,B_G})
                           (OT_R1<: OTSecurity.OTPSec.Rand1_t {A2,B_OT2,B_G})
                           (OT_R2<: OTSecurity.OTPSec.Rand2_t {A2,OT_R1, B_OT2,B_G}) 
                           (G_R<: SchSecurity.EncSecurity.Rand_t {A2,OT_R1,OT_R2,B_G,OT_S,B_OT2}):
      islossless OT_R1.gen =>
      islossless OT_R2.gen =>
      islossless OT_S.sim2 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A2.dist =>
      Compatibility () =>
      equiv [OTSecurity.OTPSec.Game2(OT_R1,OT_R2,OT_S,B_OT2(G_R,A2)).main ~
            Game2(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A2).main:
             ={glob A2,glob G_R,glob OT_S,glob OT_R1,glob OT_R2,glob G_S} ==> ={res}].
    proof.
      move => OT_R1genL OT_R2genL OT_Ssim2L G_RgenL G_SsimL A2distL compat; proc.
      inline B_OT2(G_R,A2).gen_query OTSecurity.OTPSec.Game2(OT_R1, OT_R2, OT_S, B_OT2(G_R, A2)).game Game2(PFE_R1(OT_R1), PFE_R2(OT_R2, G_R), PFE_S(G_R, G_S, OT_S), A2).game.
      seq 4 3: (x1{1} = i1{2} /\ i20{1} = i2{2} /\ (fn{1},x2{1})= i20{1} /\
              ={glob A2,glob OT_S,glob OT_R1,glob OT_R2,glob G_R,glob G_S,b}).
        by wp; call (_: true); wp; rnd; skip; smt.
      case (validInputs i1{2} i2{2}); last first.
      (*! validInputs *)
        rcondt{2} 1=> //.
        rcondt{1} 7; first by move => &m; wp; call (_: true); wp; skip; smt.
        by wp; rnd; wp; call{1} G_RgenL.
    (* validInputs *)
       rcondf{2} 1=> //.
       rcondf{1} 7; first by move => &m; wp; call (_: true); wp; skip; smt.
       inline PFE_R1(OT_R1).gen PFE_R2(OT_R2,G_R).gen PFE_S(G_R,G_S,OT_S).sim2 B_OT2(G_R,A2).dist.
       case (b{1}).
       (* case: b = 1 *)
         rcondt{1} 7; first by move => &m; wp; call (_: true).
         rcondt{2} 1=> //.
         wp; call (_: true).
         swap{2} 6 -1.
         wp; call (_: true).
         swap{2} [4..5] -2.
         wp; call (_: true).
         wp; call (_: true).
         wp; skip; progress.
         by smt.
           by rewrite H4 /= /phi2 /fst /snd /snd /=; smt.
           by rewrite H4 /= /snd /fst /prot /fst /=; smt.
       (* case: b = 0 *)
         rcondf{1} 7; first by move => &m; wp; call (_: true).
         rcondf{2} 1=> //.
         wp; call (_: true).
         wp; call (_: true).
         wp; call (_: true).
         by wp; skip; progress; smt.
    qed.

    (**********************************)
    (*         Main theorem           *)
    (**********************************)
    (**
      We have reduced the security of the SFE/PFE protocol to the security of the garbling
      scheme and OT protocol that compose it. Now, we prove that the advantage of an
      adversary that attacks the SFE/PFE protocol is related with the advantages of
      an adversary that attacks the OT protocol and the garbling scheme. 
    *)
    lemma PFE_Security_sec (A1 <: Adv1_t {SchSecurity.EncSecurity.Game_SIM,B_OT1,B_G})
                           (A2 <: Adv2_t {SchSecurity.EncSecurity.Game_SIM,B_OT2,B_G})
                           (OT_S <: OTSecurity.OTPSec.Sim_t {A1,A2,B_OT1,B_OT2,B_G})
                           (G_S <: SchSecurity.EncSecurity.Sim_SIM_t {A1,A2,OT_S,B_G})
                           (OT_R1 <: OTSecurity.OTPSec.Rand1_t {A1,A2,B_OT1,B_OT2,B_G,G_S,OT_S})
                           (OT_R2 <: OTSecurity.OTPSec.Rand2_t {A1,A2,OT_R1,B_OT1,B_OT2,B_G,G_S,OT_S}) 
                           (G_R <: SchSecurity.EncSecurity.Rand_t {A1,A2,OT_R1,OT_R2,B_G,OT_S,G_S,B_OT1,B_OT2})
                           &m epsOT1 epsOT2 epsG:
      islossless OT_R1.gen =>
      islossless OT_R2.gen =>
      islossless OT_S.sim1 =>
      islossless OT_S.sim2 =>
      islossless G_R.gen =>
      islossless G_S.simm =>
      islossless A1.gen_query =>
      islossless A1.dist =>
      islossless A2.gen_query =>
      islossless A2.dist =>
      Compatibility () =>
      (* OT_Correct *)
      OTSecurity.OTPSec.Correct () =>
      (* OT Security *)
      `|2%r * Pr[OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).main()@ &m:res] - 1%r| <= epsOT1 =>
      `|2%r * Pr[OTSecurity.OTPSec.Game2(OT_R1,OT_R2,OT_S,B_OT2(G_R,A2)).main()@ &m:res] - 1%r| <= epsOT2 =>
      (* Scheme Security *)
      `|2%r * Pr[SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).main()@ &m:res] - 1%r| <= epsG =>
      (* PFE/SFE Security *)
      `|2%r * Pr[Game1(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A1).main()@ &m:res] - 1%r| <= epsOT1 + epsG /\
      `|2%r * Pr[Game2(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A2).main()@ &m:res] - 1%r| <= epsOT2.
    proof.
      move => OT_R1genL OT_R2genL OT_Ssim1L OT_Ssim2L G_RgenL G_SsimL A1genL A1distL
              A2genL A2distL compat OT_correct OTsec1 OTsec2 Gsec.
      cut B_OT1gen_ll := B_OT1_gen_ll G_R A1 _ _=> //.
      cut B_OT1dist_ll := B_OT1_dist_ll G_R A1 _=> //.
      cut B_Ggen_ll := B_G_gen_ll OT_S A1 _=> //.
      cut B_Gdist_ll := B_G_dist_ll OT_S A1 _ _=> //.
      cut B_OT2gen_ll := B_OT2_gen_ll G_R A2 _ _=> //.
      cut B_OT2dist_ll := B_OT2_dist_ll G_R A2 _=> //.
      split.
      (* Game1 *)
        cut real_le_trans: forall (a b c:real), a <= b => b <= c => a <= c by smt.
        apply (real_le_trans _ 
              (`|2%r * Pr[SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).main() @ &m : res] - 1%r|
              +`|2%r * Pr[OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).main() @ &m : res] - 1%r| )); last smt.
        cut real_abs_sum : forall (a b c:real), a = b + c => `|a| <= `|b| + `|c| by smt.
        apply real_abs_sum.
        rewrite (SchSecurity.EncSecurity.SGame_adv &m (B_G(OT_S,A1)) G_S G_R) //.
        rewrite (OTSecurity.OTPSec.Game1_adv &m (B_OT1(G_R,A1)) OT_S OT_R1 OT_R2) //.
        rewrite (Game1_real_pr A1 OT_S G_S OT_R1 OT_R2 G_R &m) //.
        rewrite (Game1_hybrid_pr A1 OT_S G_S OT_R1 OT_R2 G_R &m) //.
        rewrite -(Game1_ideal_pr A1 OT_S G_S OT_R1 OT_R2 G_R &m) //.
        rewrite (Game1_adv &m A1 (PFE_S(G_R,G_S,OT_S)) (PFE_R1(OT_R1)) (PFE_R2(OT_R2,G_R))) //.
          by apply (PFE_R1_ll OT_R1).
          by apply (PFE_R2_ll OT_R2 G_R).
        apply (PFE_Ssim1_ll G_R G_S OT_S).
          by apply G_SsimL.
          by apply OT_Ssim1L.
        by smt.
      (* Game2 *)
        cut <-: (Pr[OTSecurity.OTPSec.Game2(OT_R1,OT_R2,OT_S,B_OT2(G_R,A2)).main()@ &m:res] =
                Pr[ Game2(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A2).main()@ &m:res ]).
          byequiv (Reduction2 A2 OT_S G_S OT_R1 OT_R2 G_R _ _ _ _ _ _ _)=> //.
        smt. 
    qed.
  end section.

  (** Pretty-print version of the lemma above *)
  lemma PFE_Security:
    Compatibility () =>
    (* OT_Correct *)
    OTSecurity.OTPSec.Correct () =>
    (* OT and Scheme Security *)
    forall (OT_R1 <: OTSecurity.OTPSec.Rand1_t {B_OT1,B_OT2,B_G})
           (OT_R2 <: OTSecurity.OTPSec.Rand2_t {OT_R1,B_OT1,B_OT2,B_G}) 
           (OT_S <: OTSecurity.OTPSec.Sim_t {B_OT1,B_OT2,B_G,OT_R1,OT_R2})
           (G_R <: SchSecurity.EncSecurity.Rand_t {OT_R1,OT_R2,B_G,OT_S,B_OT1,B_OT2})
           (G_S <: SchSecurity.EncSecurity.Sim_SIM_t {OT_S,B_G,OT_R1,OT_R2,G_R})
           (A1 <: Adv1_t {SchSecurity.EncSecurity.Game_SIM,B_OT1,B_G,OT_R1,OT_R2,OT_S,G_R,G_S})
           (A2 <: Adv2_t {SchSecurity.EncSecurity.Game_SIM,B_OT2,B_G,OT_R1,OT_R2,OT_S,G_R,G_S})
           &m epsOT1 epsOT2 epsG,
    islossless OT_R1.gen =>
    islossless OT_R2.gen =>
    islossless OT_S.sim1 =>
    islossless OT_S.sim2 =>
    islossless G_R.gen =>
    islossless G_S.simm =>
    islossless A1.gen_query =>
    islossless A1.dist =>
    islossless A2.gen_query =>
    islossless A2.dist =>
    (* OT Security *)
    (`|2%r * Pr[OTSecurity.OTPSec.Game1(OT_R1,OT_R2,OT_S,B_OT1(G_R,A1)).main()@ &m:res] - 1%r| <= epsOT1
    /\ `|2%r * Pr[OTSecurity.OTPSec.Game2(OT_R1,OT_R2,OT_S,B_OT2(G_R,A2)).main()@ &m:res] - 1%r| <= epsOT2) =>
    (* Scheme Security *)
    `|2%r * Pr[SchSecurity.EncSecurity.Game_SIM(G_R,G_S,B_G(OT_S,A1)).main()@ &m:res] - 1%r| <= epsG  =>
    (* PFE/SFE Security *)
    `|2%r * Pr[Game1(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A1).main()@ &m:res] - 1%r| <= epsOT1 + epsG /\
    `|2%r * Pr[Game2(PFE_R1(OT_R1),PFE_R2(OT_R2,G_R),PFE_S(G_R,G_S,OT_S),A2).main()@ &m:res] - 1%r| <= epsOT2.
  proof. 
    move=> compat OTcorrect OT_R1 OT_R2 OT_S G_R G_S A1 A2
         &m epsOT1 epsOT2 epsG
         OT_R1genL OT_R2genL OT_Ssim1L OT_Ssim2L G_RgenL G_SsimL
         A1genL A1distL A2genL A2distL
         [OTsec1 OTsec2] Gsec.
    by apply(PFE_Security_sec A1 A2 OT_S G_S OT_R1 OT_R2 G_R &m epsOT1 epsOT2 epsG). 
  qed.

end SFE.
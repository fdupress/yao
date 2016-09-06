(** Definition of a concrete OT protocol *)

require import Bool.
require import Int.
require import Real.
require import Distr.
require import Pair.
require import List.
require import Array.

require (*--*) OT.
require (*--*) OTSec.

require import Prime_field.
require import Cyclic_group_prime.

require (*--*) EntropySmoothing.
require (*--*) DDH.

require        ExtWord.

require import ArrayExt.

import Darray.
(**
  The protocol is an adaptation of the
  protocol presented at section 3 of "Efficient Oblivious Transfer
  Protocols" (M. Naor & B. Pinkas). The original protocol has been
  adapted to support simmultaneous transfers. Moreover, we have changed
  the security proof to the standard model to minimise interferences
  on the remaining development (the original proof was in the ROM). 

  The protocol is the following: let G be a group of prime order q
  and g be a generator of G.

  Sender Input: list of pairs of messages (length n)
  Sender Output: none
  Chooser Input: choice string (length n) sigma.
  Chooser Output: list of selected messages

  Protocol Execution: (i \in  1..n)

  1 - Sender:

    hkey <$- HashKey
    C[i] <$- G

    send msg1=(hkey, C) to chooser

  2 - Chooser:

    X[i] <$- [0..q-1]
    PK_(sigma[i])[i] = g^X[i]
    PK_(1 - sigma[i])[i] = C[i] / PK_(sigma[i])[i]

    send msg2=PK_0 to sender

  3 - Sender:

    PK_1[i] = C[i] / PK_0[i]
    r <$- [0..q-1]
    E_0[i] = H(hkey, PK_0[i]^r) (+) M_0[i]
    E_1[i] = H(hkey, PK_1[i]^r) (+) M_1[i]

    send msg3=(g^r, E0, E1) to chooser

  4 - Chooser:

    result[i] = H(hkey, (g^r)^X[i]) (+) E_(sigma[i])


  Each protocol step (msg1..msg3) is specified by (pure/deterministic)
  operators. Randomness is generated externally and passed explicitly
  to each protocol step. Beside the messages, these operators produce
  also the state that is kept by each party.

    msg1: sender_intput * sender_rand1 -> sender_state * msg1_type
    msg2: chooser_input * chooser_rand * msg1_type -> chooser_state * msg2_type
    msg3: sender_state * sender_rand2 * msg2_type -> msg3_type
    res: chooser_state * msg3_type -> chooser_output

  The full protocol can then be described as:

  Protocol(sender_inp, chooser_inp) =
  [ rs <$- SenderRandGen;
    rc <$- ChooserRandGen;
    (st_s, m1) = msg1(sender_inp, fst rs);
    (st_c, m2) = msg2(chooser_inp, rc, m1);
    m3 = msg3(st_s, snd rs, m2);
    res = res(st_c, m3);
  ]

  The sender's view is (rs, (m1,m2,m3)).
  The chooser's view is (rc, (m1,m2,m3)).
  The (chooser's) output is res.
*)
theory SomeOT.

  (** Max size of the bitstrings involved in the OT protocol *)
  op max_size: int. 

  (** Bit strings (words) to be used in the protocol *)
  clone import ExtWord as W.
  op ( ^^ ) (w:word) = ( ^ ) w.
 
  (** Decision Diffie-Hellman assumption for security proof *)
  clone DDH.DDHn as DDHn with op nmax = max_size.

  (** 
    Instantiation of an entropy-smoothing hash function
    for elements of the group where the DDH problem is
    hard 
  *)
  clone EntropySmoothing.ESn as ESn with
    type dom_t = group,
    op ddom = Dgroup.dgroup,
    type codom_t = word,
    op dcodom = Dword.dword,
    type hkey_t = word,
    op dkey = Dword.dword,
    op nmax = max_size.

  (** Hash function *)
  op H = ESn.H.hash.

  (** Randomness types *)
  type rand1_s_t = (gf_q array * ESn.hkey_t).
  type rand2_s_t = gf_q.
  type rand_c_t = gf_q array.

  (** State types *)
  (**
    States represent the information that is kept by both
    parties during the exeuction of the OT protocol.
    
    The sender keeps its input, the array C and the key to the 
    hash function.

    The receiver kepts its input, the hash key and the
    the array X
  *)
  (** Sender state *)
  type st_s_t = (word * word) array * group array * ESn.hkey_t.
  (** Chooser state *)
  type st_c_t = bool array * ESn.hkey_t * gf_q array.

  (** Message types *)
  (**
    Messages represent each step of the protocol.

    In the first step, the sender sends to the receiver
    the hash key and the array C

    In the second step, the receiver sends to the sender
    the array PK0
    
    Finally, the sender sends to the receiver g^r, E0 and
    E1
  *)
  (** Message 1 *)
  type msg1_t = ESn.hkey_t * group array.
  (** Message 2 *)
  type msg2_t = group array.
  (** Message 3 *)
  type msg3_t = group * (word*word) array.

  (**
    Auxiliary function that performs group exponentiation
    over a vector of elements of the Galois field
  *)
  op gpow (xs:gf_q array) : group array = map (fun x, g^x) xs.

  (** Computation of the PK_0 array *)
  op pk0s (inp:bool array) (gcs:group array) (xs:gf_q array) : group array =
    mapi (fun k sigma, if sigma then gcs.[k] / g^xs.[k] else g^xs.[k]) inp.

  (**
    First step of the protocol.

    The sender computes the array C and the hash key and
    sends to the receiver its state and (C, hkey).
  *)
  op msg1 (inp:(word * word) array) (r:rand1_s_t) : st_s_t * msg1_t =
    let (cs, hkey) = r in 
    let gcs = gpow cs in
    ((inp, gcs, hkey), (hkey, gcs)).

  (**
    Second step of the protocol.
      
    The receiver generates PK0 array and sends to the sender its
    state and PK0.
  *)
  op msg2 (inp:bool array) (r:rand_c_t) (m1:msg1_t) : st_c_t * msg2_t =
    let (hkey, gcs) = m1 in ((inp, hkey, r), pk0s inp gcs r).

  (**
    Last communication of the protocol.
    
    The sender generates r and sends to the receiver g^r,
    E0 and E1.
  *)
  op msg3 (st:st_s_t) (r:gf_q) (m2:msg2_t) : msg3_t =
    let (inp, gc, hkey) = st in
    let e = mapi (fun k m, ((H hkey (m2.[k]^r)) ^^ (fst m)
                           ,(H hkey ((gc.[k] / m2.[k])^r)) ^^ (snd m)))
                 inp in
    (g^r, e).

  (**
    The protocol ends with the receiver obtaining (X_1, ..., X_n).
  *)
  op result (st:st_c_t) (m3:msg3_t) : word array =
    let (inp, hkey, x) = st in
    mapi (fun k sigma, (H hkey ((fst m3)^x.[k]))
             ^^ if sigma then snd (snd m3).[k] else fst (snd m3).[k])
         inp.

  (** Protocol execution *)
  (**
    Concatenation of all the operations described above.
  *)
  op ot_prot (inp_c:bool array) (r_c:rand_c_t) (inp_s:(word * word) array) (r_s:rand1_s_t * rand2_s_t)
  : (msg1_t * msg2_t * msg3_t) * (word array * unit) = 
    let (st_s, m1) = msg1 inp_s (fst r_s) in
    let (st_c, m2) = msg2 inp_c r_c m1 in
    let m3 = msg3 st_s (snd r_s) m2 in
    let outcome = result st_c m3 in
    ((m1, m2, m3), (outcome, ())).

  (** Instantiation of the OT protocol and of its security definitions *)
  clone import OTSec.OTSecurity with
    type OT.msg_t = word,
    type OT.rand1_t = rand_c_t,
    type OT.rand2_t = rand1_s_t * rand2_s_t,
    type OT.conv_t = msg1_t * msg2_t * msg3_t,
    op OT.prot = ot_prot,
    op OT.max_size = max_size.

  import OTPSec.
  import Protocol.

  (********************
     CORRECTNESS PROOF
   ********************)
  lemma ot_correct: Correct ().
  proof.
    rewrite /Correct /validInputs /prot /f /OT.prot /ot_prot=> i1 r1 i2 r2 H1 H2.
    rewrite (pairS (fst r2)) /=
            (pairS (msg1 i2 (fst (fst r2), snd (fst r2)))) /=
            (pairS (msg2 i1 r1 (snd (msg1 i2 (fst (fst r2), snd (fst r2)))))) /=
            !snd_pair /msg1 /msg2 /msg3 /result; rewrite /= !/fst !/snd /=.
    apply arrayP; split; first smt.
    rewrite size_offun /=.
    move => k Hk; rewrite get_mapi; first smt.
    rewrite offunifE //=.
    cut xor_idemp: forall (x y z:word), x = y => x^^(y^^z) = z.
      move => x y z ->.
      cut ->:y ^^ (y ^^ z) = (y ^^ y) ^^ z by smt.
      by rewrite /Top.SomeOT.(^^) /Top.SomeOT.(^^) xorwK xorwC xorw0.
    cut Hi1: i1.[k] \/ i1.[k] = false by (by case i1.[k]).
    elim Hi1 => Hi1; rewrite Hi1 /=.
      rewrite get_mapi //= /pk0s; first by smt.
      rewrite get_mapi /=; first smt.
      rewrite Hi1 /= ?fst_red ?snd_red xor_idemp; last smt.
      cut ->: g ^ r2.`2 ^ r1.[k] = g ^ r1.[k] ^ r2.`2.
        rewrite? group_pow_mult.
        rewrite gf_q_mult_comm.
        by reflexivity.
      congr=> //; congr=> //.
      pose x:= (gpow r2.`1.`1).[k].    
      by rewrite -(div_def _ (g^r1.[k])) /Prime_field.(-) group_pow_log
               -(div_def) group_pow_log /Prime_field.(-)
               gf_q_opp_distr gf_q_minus_minus gf_q_add_assoc gf_q_add_minus gf_q_add_unit.
    rewrite /pk0s ?get_mapi //=; first by smt. rewrite !get_mapi //=; first by smt.
    rewrite Hi1 /=.
    cut ->: H r2.`1.`2 (g ^ r2.`2 ^ r1.[k]) = H r2.`1.`2 (g ^ r1.[k] ^ r2.`2).
      rewrite? group_pow_mult.
      rewrite gf_q_mult_comm.
      by reflexivity.
    by smt.
  qed.

  (** Random generators *)
  (** 
    Random generators generate randomness according to leakage information.
  *)
  module R1: Rand1_t = {
    proc gen(i1info:leak1_t): rand1_t = {
      var r:rand1_t;

      r = $Darray.darray Dgf_q.dgf_q i1info;
      return r;
    }
  }.

  module R2 : Rand2_t = {
    proc gen(i2info:leak2_t): rand2_t = {
      var c:gf_q array;
      var k:ESn.hkey_t;
      var r:gf_q;

      c = $Darray.darray Dgf_q.dgf_q i2info;
      k = $ESn.dkey; 
      r = $Dgf_q.dgf_q;
    return ((c,k),r);
    }
  }.

  (** Simulator *)
  (**
     A simulator is defined for both parties.

     A simulator must simulate the execution of an OT protocol for a party, with 
     respect to the input of that party, the expected output and the leakage of the
     input of the other party. The output of the simulator is an execution of the protocol (a view)
     that would produce the expeted output of the party given its input and with information
     of the input of the other party.

     For party P1, the simulator takes the leakage of party P2 (size of its input) and
     creates a fake array of tokens. After, it will parse the selection string (input of 
     P1) to produce either a true value for msg3 or a fake one.

     For party P2, the simulator takes the leakage of party P1 (size of its input) and
     generates a fake input of party P1. After, it simulates the OT protocol with the
     fake input.
  *)
  module S : Sim_t = {
    proc sim1(i1:input1_t,o1:output1_t,l2:leak2_t): view1_t = {
      var r1: rand1_t;
      var r2: rand2_t;
      var efake: word array;
      var cs: gf_q array;
      var hkey: ESn.hkey_t;
      var r: gf_q;
      var es: (word*word) array;

      r1 = R1.gen(phi1(i1));
      r2 = R2.gen(l2);
      efake = $Darray.darray ESn.dcodom l2;

      cs = fst (fst r2);
      hkey = snd (fst r2);

      r = snd r2;
      es = mapi (fun k m, (if i1.[k]
                           then efake.[k]
                           else H hkey (g^r^r1.[k]) ^^ m
                          ,if i1.[k]
                           then H hkey (g^r^r1.[k]) ^^ m
                           else efake.[k])) o1;

      return (r1,((hkey,gpow cs), pk0s i1 (gpow cs) r1, (g^r,es)));
    }

    proc sim2(i2:input2_t,o2:output2_t,l1:leak1_t): view2_t = {
      var r1:rand1_t;
      var r2:rand2_t;
      var i1fake:bool array;

      r1 = R1.gen(l1);
      r2 = R2.gen(phi2 i2);
      i1fake = offun (fun k, true) l1;

      return (let (st_s, m1) = msg1 i2 (fst r2) in
              let (st_c, m2) = msg2 i1fake r1 m1 in
              let m3 = msg3 st_s (snd r2) m2 in
              (r2,(m1, m2, m3)));
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)
  
  lemma R1_lossless: islossless R1.gen.
  proof.
    proc => //; rnd; skip; progress.
    change (Distr.weight ((Darray.darray (Dgf_q.dgf_q) i1info{hr})) = 1%r).
    by case (i1info{hr} < 0); smt. 
  qed.

  equiv R1_stateless: R1.gen ~ R1.gen: ={i1info} ==> ={glob R1, res} by sim.

  lemma R2_lossless: islossless R2.gen.
  proof.
    proc => //; do!rnd; skip; progress.
    by apply Dgf_q.lossless.
    by change (Distr.weight ESn.dkey = 1%r); apply Dword.lossless.
    change (Distr.weight ((Darray.darray (Dgf_q.dgf_q) (i2info{hr}))) = 1%r).
    by case (i2info{hr} < 0); smt.
  qed.

  equiv R2_stateless: R2.gen ~ R2.gen: ={i2info} ==> ={glob R2, res} by sim.

  lemma S1_lossless: islossless S.sim1.
  proof.
    proc => //; wp; rnd.
    call R2_lossless.
    call R1_lossless.
    skip; progress.
    change (Distr.weight (Darray.darray ESn.dcodom (l2{hr})) = 1%r).
    by smt. 
  qed.

  lemma S2_lossless: islossless S.sim2.
  proof.
    proc => //; wp.
    call R2_lossless.
    by call R1_lossless.
  qed.

  equiv S1_stateless: S.sim1 ~ S.sim1: ={i1,o1,l2} ==> ={glob S, res}.
  proof.
    proc => //; wp; rnd.
    call R2_stateless.
    by call R1_stateless.
  qed.
 
  equiv S2_stateless: S.sim2 ~ S.sim2: ={i2,o2,l1} ==> ={glob S, res}.
  proof.
    proc => //; wp.
    call R2_stateless.
    by call R1_stateless.
  qed.

  (*********************)
  (* Security proof    *)
  (*********************)
  (**
    Being an OT protocol a special case of a two-party protocol,
    its security can be instantiated to the security of the
    two-party protocol. Therefore, we need to prove that the OT 
    protocol "follows" the same security games of the abstract
    two-party protocol.

    The OT protocol is build on top of an ES hash function and
    on an extension to DDH assumption for arrays. Therefore,
    using the adveraries that attack these assumptions, one 
    adversary must not be able to know any more information
    about the protocol than the one that is released during 
    its execution. This can be putted into a reduction argument:
    the security of the OT protocol can be reduced to the 
    ES-security of the hash function and to the DDH-security
    of the group used in the protocol. In terms of games, this
    means that we need to prove the equivalence between the
    game that attacks the protocol and between the games that
    attack the security assumptions.
  *)
  
  section.

    (****************************)
    (*       ADVERSARIES        *)
    (****************************)

    (** Adversary attacking the DDH assumption for arrays *)
    (**
      This adversary will try to break the DDH assumption using 
      one adversary that attacks the SIM security of the scheme.

      The adversary attacking the DDH assumption starts by using
      the adversary attacking the protocol to generate its query.
      After, it will generate all the set up of the OT protocol
      but, depending on the values of the selection bit string,
      it will hash the value g^x^y or a random value (simulation).
      It ends by using the protocol adversary to distinguish between
      the two exeuctions. If the adversary succeeds in distinguish 
      the two executions, then the DDH assumption is broken.
    *)
    module DDHn_A(A1:Adv1_t): DDHn.Adv_t = {
      var i1:input1_t
      var i2:input2_t

      proc choose_n() : int = {
        (i1,i2) = A1.gen_query();
        return size i1;
      }

      proc solve(gx:group, gyzs:(group*group) array) : bool = {
        var hkey:ESn.hkey_t;
        var xs:rand1_t;
        var gcs:group array;
        var pks:group array;
        var es:(word*word) array;
        var guess:bool;

        if (validInputs i1 i2) {
          hkey = $ESn.dkey;
          xs = R1.gen(phi1(i1));
          gcs = mapi (fun k gyz, g^xs.[k] * fst gyz) gyzs;
          pks = pk0s i1 gcs xs;
          es = mapi (fun k m, (if i1.[k]
                               then H hkey (snd gyzs.[k]) ^^ fst m
                               else H hkey (gx^xs.[k]) ^^ fst m
                              ,if i1.[k]
                               then H hkey (gx^xs.[k]) ^^ snd m
                               else H hkey (snd gyzs.[k]) ^^ snd m))
                    i2;
          guess = A1.dist((xs,((hkey,gcs),pks, (gx,es))));
        } else 
          guess = ${0,1};
        return guess;
      }
    }.

    (** Adversary attacking the ES assumption for the hash function *)
    (**
      This adversary will try to break the ES assumption using 
      one adversary that attacks the SIM security of the scheme.
        
      The adversary attacking the ES assumption starts by using
      the adversary attacking the protocol to generate its query.
      After, it will generate all the set up of the OT protocol
      but, depending on the values of the selection bit string,
      it will hash the value g^x^y or it will generate a random
      bit string for the encoding key.
      It ends by using the protocol adversary to distinguish between
      the two exeuctions. If the adversary succeeds in distinguish 
      the two executions, then the ES assumption is broken.
    *)
    module ESn_A(A1: Adv1_t): ESn.Adv_t = {
      var i1:input1_t
      var i2:input2_t

      proc choose_n() : int = {
        (i1,i2) = A1.gen_query();
        return size i1;
      }

      proc solve(key: ESn.hkey_t, a: word array) : bool = {
        var cs:gf_q array;
        var gcs:group array;
        var xs:rand1_t;
        var pks:group array;
        var r:gf_q;
        var es:(word*word) array;
        var guess:bool;

        if (validInputs i1 i2) {
          cs = $Darray.darray Dgf_q.dgf_q (size i1);
          xs = $Darray.darray Dgf_q.dgf_q (size i1);
          r = $Dgf_q.dgf_q;
          gcs = gpow cs;
          pks = pk0s i1 gcs xs;
          es = mapi (fun k m, (if i1.[k]
                               then a.[k] ^^ fst m
                               else H key (g^xs.[k]^r) ^^ fst m
                              ,if i1.[k]
                               then H key (g^xs.[k]^r) ^^ snd m
                               else a.[k] ^^ snd m))
                    i2;
          guess = A1.dist((xs,((key,gcs),pks, (g^r,es))));
        } else 
          guess = ${0,1};
        return guess;
      }
    }.

    (***************************)
    (* Lossnessness properties *)
    (***************************)
    
    lemma DDHn_A_choose_ll (A1<: Adv1_t):
      islossless A1.gen_query =>
      islossless DDHn_A(A1).choose_n.
    proof.
      by move => A1genqueryL; proc; call A1genqueryL.
    qed.

    lemma DDHn_A_solve_ll (A1<: Adv1_t):
      islossless A1.dist =>
      islossless DDHn_A(A1).solve.
    proof.
      move => A1distL; proc => //.
      case (validInputs DDHn_A.i1 DDHn_A.i2); last first.
        by rcondf 1 => //; rnd; skip; smt.
        by rcondt 1 => //;
          call A1distL; wp;
          call R1_lossless;
          rnd; skip; smt.
    qed.

    lemma ESn_A_choose_ll (A1<: Adv1_t):
      islossless A1.gen_query =>
      islossless ESn_A(A1).choose_n.
    proof.
      by move => A1genqueryL; proc => //; call A1genqueryL.
    qed.

    local lemma ESn_A_solve_ll (A1<: Adv1_t):
      islossless A1.dist =>
      islossless ESn_A(A1).solve.
    proof.
      move => A1distL; proc => //.
      case (validInputs ESn_A.i1 ESn_A.i2); last first.
      by rcondf 1=> //; rnd; skip; smt.
      by rcondt 1=> //;
        call A1distL; wp;
        do!rnd; skip; smt.
    qed.

    (**********************************)
    (*       Party 1 simulation       *)
    (**********************************)
    (**
      The security definitions for party P1 state, informally,
      that the execution of the protocol does not release any
      more information about the ES and DDH assumptions other
      than the one that is admissible.
    *)
 
    (** Auxiliar operation that either substracts or sums every 
        value of an array by another *) 
    op xinv side (xs:gf_q array) (cs:gf_q array) : gf_q array =
      mapi (fun k c, if side then c-xs.[k] else c+xs.[k]) cs.
        
    (** xinv is bijective *)
    local lemma xinv_bij (sigma:bool) cs xs:
      xinv sigma cs (xinv (!sigma) cs xs) = xs.
    proof. 
    delta => /=.
    rewrite mapi_mapi /=. 
    apply arrayP; split; first by smt.
    rewrite size_mapi => k Hk.
    rewrite get_mapi //=; smt.
    qed.

    (** xinv size *)
    local lemma xinv_size sigma cs xs:
      size (xinv sigma cs xs) = size xs by [].

    (** Auxiliary lemma that states that if two elements are in the
      support of an uniform distribution, then their probability is
      the same *)
    local lemma uniform_pr_eq d (y z: 'x) :
      is_uniform d => support d y => support d z => mu_x d y = mu_x d z by []. 

    (** 
      The security game of the OT protocol is indistinguishable from
      the DDH for arrays game instantiated with the adversary defined
      above. Informally, this means that the execution of the OT protocol
      does not reveal any information about the hash function other than
      the one admissible by the DDH assumption.
    *)
    local lemma Game1_real_equiv (A1<: Adv1_t {DDHn_A}):
      islossless A1.dist =>
      equiv [ Game1(R1,R2,S,A1).game ~ DDHn.Game(DDHn_A(A1)).game:
              ={glob A1,glob R1,glob R2} /\ b{1} /\ b{2} ==> ={res}].
    proof.
      move => A1distL; proc => //; inline DDHn_A(A1).choose_n DDHn_A(A1).solve S.sim1.
      seq 1 1 : (b{1} /\ b{2} /\
               i1{1} = DDHn_A.i1{2} /\
               i2{1} = DDHn_A.i2{2} /\
               ={glob A1,glob R1,glob R2}).
        by call (_: true).
      if {1}.
        rcondf {2} 9.
          by move => &m; wp; do 3!rnd; wp; skip; progress.
          by wp; rnd; wp; do 3!rnd{2}; wp; skip; progress; smt.
        rcondt {2} 9.
          by move => &m; wp; do 3! rnd; wp; skip; progress.
      rcondt {1} 1; first by move => &m; skip; progress.
      rcondt {2} 6; first by move => &m; do 3! rnd; wp; skip; progress; smt.
      swap {2} 10 -9; inline R2.gen.
      seq 1 1: (b{1} /\ b{2} /\ i1{1} = DDHn_A.i1{2} /\ i2{1} = DDHn_A.i2{2}
              /\ ={glob A1,glob R1,glob R2} /\ validInputs i1{1} i2{1} /\ r1{1}=xs{2}).
        by call R1_stateless.
      wp; call (_: true).
      swap {2} 3 2; swap {2} 4 -1; swap {2} 9 -4.
      wp; do 2!rnd.
      rnd (xinv true r1{1}) (xinv false r1{1}).
      rnd{2}; wp; skip.
      move => &1 &2 [Hb1 [Hb2 [-> [-> [[eqA] [eqR1] eqR2 [Hval ->]]]]]].
      cut Hsimpl1: forall (x y:gf_q), x = y + (x - y).
        by move=> x y; rewrite /Prime_field.(-) gf_q_add_assoc gf_q_add_comm gf_q_add_assoc
                            (gf_q_add_comm (-y)) gf_q_add_minus gf_q_add_unit.
      cut Hsimpl2: (0 <= size DDHn_A.i1{2} <= DDHn.nmax)=true by smt.
      cut ->: phi2 DDHn_A.i2{2} = size DDHn_A.i1{2} by smt.
      progress.
        by smt.
        by smt.
      rewrite Hsimpl2 /=.
      rewrite (uniform_pr_eq (Darray.darray Dgf_q.dgf_q (size DDHn_A.i1{2})) yR (xinv false xs{2} yR)); smt.
      by apply Darray.supp_full; expect 3 smt.
      by smt.
      rewrite Hsimpl2 /=.     
      rewrite /gpow; apply arrayP; split; first by smt.
      rewrite size_map=> k Hk. rewrite mapE // get_mapi /=.
      by rewrite size_offun; smt.
      rewrite offunifE /=.
      cut ->: (if 0 <= k < size DDHn_A.i1{2} then
              (g ^ (xinv true xs{2} cL).[k], g ^ (r0L * (xinv true xs{2} cL).[k]))
              else Option.witness) = (g ^ (xinv true xs{2} cL).[k], g ^ (r0L * (xinv true xs{2} cL).[k])) by smt.  
      by rewrite fst_pair /xinv /= get_mapi //= group_pow_add; congr; smt.
      apply arrayP; split; first smt.
      rewrite /pk0s size_mapi //= => k Hk.
      rewrite !get_mapi //= !get_mapi //=. 
        by rewrite size_offun; smt.
      rewrite  offunifE. 
      cut ->: (if 0 <= k < if 0 <= size DDHn_A.i1{2} <= DDHn.nmax then size DDHn_A.i1{2} else 0 then
              (fun (k0 : int) =>
                (g ^ (xinv true xs{2} cL).[k0], g ^ (r0L * (xinv true xs{2} cL).[k0]))) k
              else Option.witness) = (fun (k0 : int) =>
                (g ^ (xinv true xs{2} cL).[k0], g ^ (r0L * (xinv true xs{2} cL).[k0]))) k by smt.
      rewrite /= !fst_pair.
      cut Hin: DDHn_A.i1{2}.[k] \/ DDHn_A.i1{2}.[k]=false.
        by case (DDHn_A.i1{2}).[k].
      elim Hin => Hin; rewrite Hin //=.
      cut k_bnd: 0 <= k < size cL by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
      by delta=> /=; rewrite get_mapi // mapE //; smt.
      apply arrayP; split; first by smt.
      move => k Hk; rewrite !get_mapi //=; first 2 smt.
      cut Hin: DDHn_A.i1{2}.[k]=true \/ DDHn_A.i1{2}.[k]=false.
        by case (DDHn_A.i1{2}).[k].
      elim Hin => Hin; rewrite Hin //=.
        rewrite offunifE. 
        rewrite /pk0s /xinv /gpow /= !snd_pair get_mapi /= 2:Hin /=; first by smt.
        split.
          congr.
          cut k_bnd: 0 <= k < size cL by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
          by rewrite get_mapi // mapE //; smt.
          move=> Hkl.
          cut k_bnd: 0 <= k < size cL by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
          rewrite mapE //=; congr.
          by rewrite -(div_def _ (g^xs{2}.[k])) /Prime_field.(-) 2!group_pow_log
                   -(div_def) 2!group_pow_log /Prime_field.(-) gf_q_opp_distr
                   gf_q_minus_minus gf_q_add_assoc gf_q_add_minus gf_q_add_unit; smt.
      rewrite Hsimpl2 /= offunifE /= ?snd_pair.
      rewrite /pk0s /gpow /= get_mapi ?Hin /=; first by smt.
      split; first by rewrite? group_pow_mult gf_q_mult_comm; reflexivity.
      move=> Hkl.
      cut k_bnd: 0 <= k < size cL by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
      rewrite /xinv mapE // get_mapi //=.
      congr; congr.
      cut ->: (if 0 <= k < size DDHn_A.i1{2} then
                 (g ^ (cL.[k] - xs{2}.[k]), g ^ (r0L * (cL.[k] - xs{2}.[k])))
                 else Option.witness) = (g ^ (cL.[k] - xs{2}.[k]), g ^ (r0L * (cL.[k] - xs{2}.[k]))) by smt.
      by rewrite -div_def /Prime_field.(-) 2!group_pow_log group_pow_mult gf_q_mult_comm.
      by smt.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game1_real_pr (A1<:Adv1_t {DDHn_A}) &m:
      islossless A1.dist =>
      Pr[Game1(R1,R2,S,A1).game(true)@ &m: res] =
      Pr[DDHn.Game(DDHn_A(A1)).game(true)@ &m: res].
    proof. by move=> A1_dist_ll; byequiv (Game1_real_equiv A1 _). qed.

    (** Auxiliary function that gets the xor of the elements of
      two arrays *)
    op xorinv (ms:word array) (xs:word array) : word array = 
      mapi (fun k x, ms.[k] ^^ x) xs.

    (** xorinv is a bijection *)
    local lemma xorinv_bij ms xs:
      xorinv ms (xorinv ms xs) = xs.
    proof.
      delta=> /=.
      rewrite mapi_mapi /=.
      apply arrayP; split; first by smt.
      rewrite size_mapi => k Hk.
      by rewrite get_mapi //= xorwA xorwK xorwC xorw0.
    qed.

    (** xorinv size *)
    local lemma xorinv_size ms xs:
      size (xorinv ms xs) = size xs by [].

    (** 
      The security game of the OT protocol is indistinguishable from
      the ES hash function game instantiated with the adversary defined
      above. Informally, this means that the execution of the OT protocol
      does not reveal any information about the hash function other than
      the one admissible by the ES assumption.
    *)
    local lemma Game1_ideal_equiv (A1<: Adv1_t {ESn_A}):
      islossless A1.dist =>
      is_lossless ESn.H.dkey =>
      equiv [ Game1(R1,R2,S,A1).game ~ ESn.Game(ESn_A(A1)).game:
              ={glob A1,glob R1,glob R2} /\ !b{1} /\ !b{2} ==> ={res} ].
    proof.
      move => A1distL ESnHdkey_ll; proc => //; inline ESn_A(A1).choose_n ESn_A(A1).solve.
      seq 1 1 : (!b{1} /\ !b{2} /\
               i1{1} = ESn_A.i1{2} /\
               i2{1} = ESn_A.i2{2} /\
               ={glob A1}).
        by call (_: true).
      if {1}.
        rcondf {2} 9.
          by move => &m; wp; do 3!rnd; wp; skip; progress.
          by wp; rnd; wp; do 3!rnd{2}; wp; skip; progress; smt. 
      rcondt {2} 9.
        by move => &m; wp; do 3! rnd; wp; skip; progress.
      rcondf {1} 1; first by move => &m; skip; progress.
      rcondf {2} 6; first by move => &m; do 3! rnd; wp; skip; progress; smt.
      inline R1.gen R2.gen S.sim1.
      swap{1} 13 -8. swap{2} 3 3. swap{2} [6..7] 3.
      wp; call (_: true).
      wp; rnd; wp; rnd.
      swap{2} 7 1; rnd; wp; rnd; wp.
      rnd (xorinv (mapi (fun k mm, if ESn_A.i1{2}.[k] then fst mm else snd mm) ESn_A.i2{2})).
      rnd{2}; wp; skip => &1 &2 /= [[Hb1 [Hb2 [-> [-> ->]]]] Hval].
      cut ->: phi1 ESn_A.i1{2} = size ESn_A.i1{2} by smt.
      cut ->: phi2 ESn_A.i2{2} = size ESn_A.i1{2} by smt.
      cut ->: 0 <= size ESn_A.i1{2} <= ESn.nmax by smt.
      progress; trivial; [smt|smt| |smt|smt| |smt].
        apply uniform_pr_eq=> //; first smt.
        by apply Darray.supp_full; expect 3 smt.
        rewrite /f !fst_pair !snd_pair /=.
        apply arrayP; split;
          first by rewrite !size_mapi size_offun; smt.
        rewrite !size_mapi !size_offun /=. 
        delta=> /= k Hk; rewrite get_mapi //=; first smt tmo=30.
        cut Hin: ESn_A.i1{2}.[k] \/ ESn_A.i1{2}.[k]=false
          by case (ESn_A.i1{2}.[k]); trivial.
        elim Hin => Hin; rewrite Hin //=.
          rewrite get_mapi //=; first by smt. 
          cut k_bnd: 0 <= k < size efakeL by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
          rewrite get_mapi //=.
          rewrite offunifE //=. 
          rewrite get_mapi //=; first by smt.
          rewrite Hin /=.
          cut ->: g ^ r3L ^ r0L.[k] = g ^ r0L.[k] ^ r3L.
            by rewrite? group_pow_mult gf_q_mult_comm; reflexivity.  
        cut ->: (if 0 <= k < size ESn_A.i2{2} then (ESn_A.i2{2}.[k]).`2
                else Option.witness) = (ESn_A.i2{2}.[k]).`2 by smt.
        by move: (efakeL.[k]) (ESn.H.hash kL (g ^ r0L.[k] ^ r3L)) => a b;
           rewrite xorwC xorwA xorwK xorwC xorw0.
        cut k_bnd_i2: 0 <= k < size ESn_A.i2{2} by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
        cut k_bnd_ef: 0 <= k < size efakeL by (move: H3; rewrite -Darray.supp_full; expect 3 smt).
        rewrite get_mapi //= get_mapi //=.
        rewrite Hin //= offunifE //= get_mapi //= Hin /=.
        cut ->: g ^ r3L ^ r0L.[k] = g ^ r0L.[k] ^ r3L.
          by rewrite? group_pow_mult gf_q_mult_comm; reflexivity. 
        cut ->: (if 0 <= k < size ESn_A.i2{2} then (ESn_A.i2{2}.[k]).`1 else Option.witness) = (ESn_A.i2{2}.[k]).`1 by smt.
        move: (efakeL.[k]) (ESn.H.hash kL (g ^ r0L.[k] ^ r3L)) => a b; split=> // _.
        by rewrite xorwC xorwA xorwK xorwC xorw0.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game1_ideal_pr  (A1<:Adv1_t {ESn_A}) &m:
      islossless A1.dist =>
      is_lossless ESn.H.dkey =>
      Pr[Game1(R1,R2,S,A1).game(false)@ &m: !res] =
      Pr[ESn.Game(ESn_A(A1)).game(false)@ &m: !res].
    proof. by move=> A1distL ESnHdkey_ll; byequiv (Game1_ideal_equiv A1 _ _). qed.
  
    (** 
      The security game of the ES assumption instantiated with the
      aversary above is indistinguishable from the security game of 
      the DDH assumption instantiated with the adversary above. 
      Informally, this means that an adversary attacking the ES security
      of the hash function using the adversary attacking the OT protocol
      learns no additional information than one adversary attacking the
      DDH security of the cyclic group using the adversary attacking the
      OT protocol.

      Intuitively, since both games are indistinguishable from Game1,
      they should be indistinguishable from one another.
    *)
    local lemma Game1_glue_equiv (A1<:Adv1_t {DDHn_A, ESn_A}):
      islossless A1.dist =>
      is_lossless ESn.H.dkey =>
      equiv [ ESn.Game(ESn_A(A1)).game ~ DDHn.Game(DDHn_A(A1)).game:
              ={glob A1} /\ b{1} /\ !b{2} ==> res{1}=!res{2}].
    proof.
      move => A1distL ESnHdkey_ll; proc => //; inline ESn_A(A1).choose_n ESn_A(A1).solve 
        DDHn_A(A1).choose_n DDHn_A(A1).solve R1.gen R2.gen.
      seq 2 2: (b{1} /\ !b{2} /\
              ESn_A.i1{1} = DDHn_A.i1{2} /\
              ESn_A.i2{1} = DDHn_A.i2{2} /\
              n{1} = size ESn_A.i1{1} /\
              ={n, glob A1}).
        by wp; call (_: true).
      case (validInputs ESn_A.i1{1} ESn_A.i2{1}); last first.
        rcondf{1} 8; first by move => &m; wp; do!rnd; wp.
        rcondf{2} 8; first by move => &m; wp; do!rnd; wp.
        wp; rnd; wp; do!(rnd{1}; rnd{2}).
        by wp; skip; progress; smt.
      rcondt{1} 8; first by move => &m; wp; do!rnd; wp.
      rcondt{2} 8; first by move => &m; wp; do!rnd; wp.
      rcondt{1} 5; first by move => &m; wp; do!rnd; wp.
      rcondf{2} 5; first by move => &m; wp; do!rnd; wp.
      wp; call (_: true).
      swap{2} 8 -6; wp.
      swap{1} 10 -7. swap{1} 10 -6. swap{2} [9..10] -5. 
      seq 4 5: (key{1} = hkey{2} /\ r{1} = x{2} /\
              xs{1} = r{2} /\ i1info{2} = phi1 DDHn_A.i1{2} /\
              b{1} /\ !b{2} /\
              ESn_A.i1{1} = DDHn_A.i1{2} /\
               ESn_A.i2{1} = DDHn_A.i2{2} /\ 
               n{1} = size ESn_A.i1{1} /\ ={n, glob A1} /\
               validInputs ESn_A.i1{1} ESn_A.i2{1}).
        by rnd; wp; rnd; rnd; wp; skip; smt.
      swap {1} 6 -5.
      wp; rnd {1}.
      rnd (Array.map Cyclic_group_prime.log) gpow.
      rnd (xinv true xs{1}) (xinv false xs{1}).
      cut Hsimpl: forall (a b:gf_q), a = b + (a + -b).
        by move=> x y; rewrite /Prime_field.(-) gf_q_add_assoc gf_q_add_comm gf_q_add_assoc
                              (gf_q_add_comm (-y)) gf_q_add_minus gf_q_add_unit.
      skip; progress=> //.
        by smt.
        apply uniform_pr_eq; first smt.
        by apply Darray.supp_full; expect 3 smt.
        by apply Darray.supp_full; expect 3 smt.
        by apply Darray.supp_full; expect 3 smt.
        by smt. 
        rewrite /gpow /map /=.
        apply arrayP; split; first smt.
        move => k Hk; rewrite mapE //=; first 2 by smt.
        rewrite mux_darray; first by smt. 
        rewrite mux_darray; first by smt.
        rewrite /gpow ?List.foldr_map /=. 
        cut ->: (if size DDHn_A.i1{2} = size zR then
   foldr (fun (x : gf_q) (z : real) => mu Dgf_q.dgf_q (pred1 x) * z) 1%r
     (filter predT (ofarray zR))
 else 0%r) = foldr (fun (x : gf_q) (z : real) => mu Dgf_q.dgf_q (pred1 x) * z) 1%r
     (filter predT (ofarray zR)) by smt.
        cut ->: (if size DDHn_A.i1{2} = size (map (fun (x : gf_q) => g ^ x) zR) then
  foldr (fun (x : ESn.dom_t) (z : real) => mu ESn.ddom (pred1 x) * z) 1%r
    (filter predT (ofarray (map (fun (x : gf_q) => g ^ x) zR)))
else 0%r) = foldr (fun (x : ESn.dom_t) (z : real) => mu ESn.ddom (pred1 x) * z) 1%r
    (filter predT (ofarray (map (fun (x : gf_q) => g ^ x) zR))) by smt.
        cut ->: (fun (x : gf_q) (z : real) => mu Dgf_q.dgf_q (pred1 x) * z) = (fun (x : gf_q) (z : real) => mu_x Dgf_q.dgf_q x * z) by rewrite /mu_x; reflexivity.
        cut ->: (fun (x : ESn.dom_t) (z : real) => mu ESn.ddom (pred1 x) * z) = (fun (x : ESn.dom_t) (z : real) => mu_x ESn.ddom x * z) by rewrite /mu_x; reflexivity. 
        cut ->: (fun (x : gf_q) (z : real) => mu_x Dgf_q.dgf_q x * z) = (fun (x : gf_q) (z : real) => 1%r/q%r * z) by apply fun_ext => a /=; apply fun_ext => b /=; rewrite Dgf_q.mu_x_def_in.
        cut ->: (fun (x : ESn.dom_t) (z : real) => mu_x ESn.ddom x * z) = (fun (x : ESn.dom_t) (z : real) => 1%r/q%r * z) by apply fun_ext => a /=; apply fun_ext => b /=; smt. 
        by rewrite ?filter_predT /map ofarrayK List.foldr_map. 
        by apply Darray.supp_full; expect 3 smt.
        rewrite /gpow /=. (*map_map /=. *)
        apply arrayP; split; first smt.
        by move => k Hk; rewrite mapE //=; smt. 
        by smt.
        delta=> /=.
        apply arrayP; split; first smt.
        rewrite size_map => k Hk.
        rewrite mapE //= get_mapi /=; first by rewrite size_offun; smt.
        rewrite offunifE /=. 
        by rewrite get_mapi //=; smt. 
        delta => /=.
        apply arrayP; split; first smt.
        rewrite size_mapi => k Hk.
        rewrite !get_mapi //=.
        cut Hin: DDHn_A.i1{2}.[k] \/ DDHn_A.i1{2}.[k]=false
          by (case (DDHn_A.i1{2}.[k])).
        elim Hin => Hin; rewrite Hin //=.
        rewrite get_mapi //=; first smt.
        rewrite offunifE //=.
        cut k_bnd: 0 <= k < size csL by (move: H4; rewrite -Darray.supp_full; expect 3 smt).
        by rewrite mapE 2:get_mapi //=; smt.
        delta=> /=.
        apply arrayP; split; first smt.
        rewrite size_mapi => k Hk.
        rewrite !get_mapi //=.
        cut Hin: DDHn_A.i1{2}.[k] \/ DDHn_A.i1{2}.[k]=false
          by (case (DDHn_A.i1{2}.[k])).
        elim Hin => Hin; rewrite Hin //=.
        rewrite offunifE /=. 
        rewrite offunifE /=.
        split; first by smt.
          move => Hc.
          cut ->: g ^ r{2}.[k] ^ x{2} = g ^ x{2} ^ r{2}.[k].
            by rewrite? group_pow_mult gf_q_mult_comm; reflexivity.
          reflexivity.
          rewrite H11 /gpow (*!map_map*) /=; progress.
          cut ->: g ^ r{2}.[k] ^ x{2} = g ^ x{2} ^ r{2}.[k].
          by rewrite? group_pow_mult gf_q_mult_comm; reflexivity.
          reflexivity.
          rewrite offunifE /=.
          congr; rewrite !mapE /=; first 2 by move: H9; rewrite -Darray.supp_full; expect 3 smt.
          cut ->: (if 0 <= k < size DDHn_A.i1{2} then (ESn.H.hash hkey{2} (g ^ log xL.[k]))%ESn.H
      else Option.witness) = (ESn.H.hash hkey{2} (g ^ log xL.[k]))%ESn.H by smt.
          congr; rewrite ?mkarray_map ?ofarrayK mapE; first by smt.
          by simplify; rewrite ?getE ?ofarrayK; smt timeout=30. 
          by smt.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game1_glue_pr (A1<:Adv1_t {DDHn_A, ESn_A}) &m:
      islossless A1.dist =>
      is_lossless ESn.H.dkey =>
      Pr[ESn.Game(ESn_A(A1)).game(true)@ &m: res] =
      Pr[DDHn.Game(DDHn_A(A1)).game(false)@ &m: !res].
    proof. by move=> A1distL ESnHdkey_ll; byequiv (Game1_glue_equiv A1 _ _). qed.

    (**********************************)
    (*       Party 2 simulation       *)
    (**********************************)
    (**
      For pary P2, the security definitions are easy: since it does not
      output anything at the end of the protocol, our only concern is that
      it can not obtain any information about the input of P1. In terms of
      views, this means that two views of party P2 are always indistinguishable
      from one another.

      In other words, this means that the probability of winning the
      game when a real execution occurs is the same probability of loosing the
      game when a simulation execution occurs.
    *)

    (** Auxiliar function that, according to a selection string, either
      outputs elements of the cyclic group *)
    op ginv (inp: bool array) (cs:gf_q array) (xs:gf_q array) : gf_q array =
      mapi (fun k x, if inp.[k] then x else cs.[k]-x) xs.

    (** ginv is a bijection *)
    local lemma ginv_bij sigma cs xs:
     ginv sigma cs (ginv sigma cs xs) = xs.
    proof.
      rewrite /ginv /ginv mapi_mapi mapi_id // => k x Hk.
      case (sigma.[k]) => H; first by smt.
      cut ->: sigma.[k]=false by rewrite neqF => /=.
      cut HH: forall (x y:gf_q), (x-y = x + -y) by smt.
      by rewrite HH; smt.
    qed.

    (** ginv size *)
    local lemma ginv_size sigma cs xs:
     size (ginv sigma cs xs) = size xs by [].

    local lemma pks_ginv (inp: bool array) (xs cs: gf_q array):
      size xs = phi1 inp =>
      size cs = phi1 inp =>
      pk0s (offun (fun k, true) (phi1 inp)) (gpow cs) (ginv inp cs xs) = pk0s inp (gpow cs) xs.
    proof. 
      rewrite /pk0s=> Hlen1 Hlen2.
      apply arrayP; split;
        first by rewrite !size_mapi size_offun; smt.
      move=> k; rewrite size_mapi size_offun max_ler; first by smt. 
      move => hk. rewrite ?get_mapi. smt. smt. simplify. cut ->: (offun (fun (_ : int) => true) (phi1 inp)).[k] <=> true by smt. simplify. case (inp.[k]) => hcase. smt full. rewrite /gpow. rewrite mapE. smt. simplify. rewrite /ginv. rewrite get_mapi. smt. simplify. smt. 
    qed.

    local lemma pks_ginv_inv (inp:bool array) (xs cs: gf_q array):
      size xs = phi1 inp =>
      size cs = phi1 inp =>
      pk0s (offun (fun k, true) (phi1 inp)) (gpow cs) xs = pk0s inp (gpow cs) (ginv inp cs xs) by [].

    (**
      P2 learns no additional information about the OT protocol other than
      admissible. It does not matter which execution occurs: a simulated one
      or a real one.
    *)
    local lemma Game2_equiv (A2<:Adv2_t):
      equiv [ Game2(R1,R2,S,A2).game ~ Game2(R1,R2,S,A2).game:
              ={glob A2} /\ b{1} /\ !b{2} ==> res{1}=!res{2}].
    proof.
      proc => //.
      seq 1 1: (b{1} /\ !b{2} /\ ={i1, i2, glob A2}).
        by call (_: true).
      if=> //; first rnd; skip; progress; smt.
      rcondt{1} 1=> //; rcondf{2} 1=> //.
      call (_: true).
      inline R1.gen R2.gen S.sim2.
      wp; rnd (*r*); rnd(*k*).
      swap {1} [4..5] -3; swap {2} [8..9] -5; swap {2} [2..4] -1.
      seq 2 3: (b{1} /\ !b{2} /\ i2{1} = i20{2} /\
              validInputs i1{1} i2{1} /\
              size c{1} = phi1 i1{1} /\
              ={i1, i2, c, glob A2}).
        rnd; wp; skip; progress=> //.
        by rewrite (Darray.supp_len (phi2 i2{2}) cL Dgf_q.dgf_q) //; smt.
      wp; rnd (ginv i1{1} c{1}) (ginv i1{2} c{2}).
      wp; skip; progress; [smt| |smt| | | |smt].
        apply uniform_pr_eq; first smt.
        by apply Darray.supp_full; expect 3 smt.
        by apply Darray.supp_full; expect 3 smt. 
        by rewrite ginv_bij; smt. 
        by rewrite pks_ginv; smt.
        by rewrite pks_ginv; smt.
    qed.

    (**
      Since the two games are equivalent, the advantage of an adversary is the same
      in both games
    *)
    local lemma Game2_pr (A2<: Adv2_t) &m:
      Pr[Game2(R1,R2,S,A2).game(true)@ &m: res] =
       Pr[Game2(R1,R2,S,A2).game(false)@ &m: !res].
    proof. by byequiv (Game2_equiv A2). qed.
  
    (**********************************)
    (*         Main theorem           *)
    (**********************************)
    (**
      We have reduced the security of this concrete OT protocol to the ES security
      of the hash function and to the DDHn assumption over the cyclic group. Now, we
      prove that the advantage of an adversary attacking the concrete OT protocol is
      related with the advantages of an adversary that attacks the ES assumption and
      the DDH assumption.
    *)
    lemma ot_is_sec (A1 <: Adv1_t {ESn_A, DDHn_A, DDHn.DDHnmax.H.Count, DDHn.DDHnmax.H.HybOrcl, DDHn.DDHnmax.K, DDHn.DDHnmax.ADDH, DDHn.ADDHnmax}) (A2 <: Adv2_t) &m:
      islossless A1.gen_query => islossless A1.dist =>
      islossless A2.gen_query => islossless A2.dist =>
      forall eps_ESn eps_DDH,
      `|2%r * Pr[ESn.Game(ESn_A(A1)).main()@ &m:res] - 1%r| <= eps_ESn =>
      `|2%r * Pr[DDH.DDH.Game(DDHn.DDHnmax.ADDH(DDHn.ADDHnmax(DDHn_A(A1)))).main()@ &m:res] - 1%r| <= eps_DDH =>
      `|2%r * Pr[Game1(R1,R2,S,A1).main()@ &m:res] - 1%r| <= eps_ESn + DDHn.nmax%r * eps_DDH /\
      `|2%r * Pr[Game2(R1,R2,S,A2).main()@ &m:res] - 1%r| <= 0%r.
    proof.
      move=> A1genL A1distL A2genL A2distL eps_ESn eps_DDH HESn HDDH; split.
      (* party 1 security *)
      cut real_le_trans: forall (a b c:real), a <= b => b <= c => a <= c by smt.
      apply (real_le_trans _ 
        (`|2%r * Pr[ESn.Game(ESn_A(A1)).main() @ &m : res] - 1%r|
        + `|2%r * Pr[DDHn.Game(DDHn_A(A1)).main() @ &m : res] - 1%r|)).
        cut real_abs_sum : forall (a b c:real), a = b + c => `|a| <= `|b| + `|c| by smt.
        apply real_abs_sum.
          rewrite (Game1_adv &m A1 S R1 R2) //.
            by apply R1_lossless.
            by apply R2_lossless.
            by apply S1_lossless.
          rewrite (ESn.Game_adv &m (ESn_A(A1))) //; first 3 smt.
            by apply (ESn_A_choose_ll A1).
            by apply (ESn_A_solve_ll A1).
          rewrite (DDHn.DDHn_adv &m (DDHn_A(A1))) //.
            by apply (DDHn_A_choose_ll A1).
            by apply (DDHn_A_solve_ll A1).
          rewrite (Game1_ideal_pr A1 &m) //.
            by smt.
          rewrite (Game1_real_pr A1 &m) //.
          rewrite (Game1_glue_pr A1 &m) //.
            by smt.
       cut:= DDHn.DDHn_adv_bound &m (DDHn_A(A1)) eps_DDH _ _ _ => //.
          by apply (DDHn_A_choose_ll A1).
          by apply (DDHn_A_solve_ll A1).
          by smt.
          cut addleM : forall (x1 x2 y1 y2:real), x1 <= x2 => y1 <= y2 => x1 + y1 <= x2 + y2 by smt.
          apply addleM; first by smt. 
      cut:= DDHn.DDHn_adv_bound &m (DDHn_A(A1)) eps_DDH _ _ _ => //.
          by apply (DDHn_A_choose_ll A1).
          by apply (DDHn_A_solve_ll A1).
      (* party 2 security *) 
      rewrite (Game2_adv &m A2 S R1 R2) //.
        by apply R1_lossless.
        by apply R2_lossless.
        by apply S2_lossless.
      by rewrite (Game2_pr A2 &m); smt.
    qed.
  end section.
end SomeOT.
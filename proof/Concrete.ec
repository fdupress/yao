require import Real.
require import Int.
require import Pair.
require import Array.

require        SFE.
require        EffSch.
require        ProjSch.
require        SomeOT.
require        Prot.
require        ProtSec.
require        SomeGarble.
require        SomeDKC.

import ArrayExt.
    
theory Concrete.
  clone import ExtWord as W.
  clone import SomeOT.SomeOT with
    theory WS <- W.
  clone import EffSch.EfficientScheme as ES with
    theory W <- W.

    import ES.ProjScheme.
    
   (* Definition of leakage for both PFE and SFE protocols *)
   op pfe_or_sfe : bool.
   
   op sch_phi (fn:Sch.Scheme.fun_t): Sch.Scheme.fun_t=
    if pfe_or_sfe
     then (* PFE: leaks the circuit's topology *)
          ( fst fn,
           map (fun x, (false,false,false,false)) (snd fn))
     else (* SFE: circuit is public *) fn.

   op leakInterface (x: Sch.Scheme.fun_t * int) : Sch.Scheme.leak_t * int = 
          let (n, m, q, aa, bb) = fst (fst x) in
          (Sch.Scheme.phi (fst x), n - (snd x)).

   type state1_t = SomeOT.st_c_t.
   type rand1_t = SomeOT.OTSecurity.OT.rand1_t.
   type state2_t = SomeOT.st_s_t * Sch.Scheme.funG_t  * Sch.Scheme.outputK_t * 
                     word array * SomeOT.rand2_s_t.
   type rand2_t = SomeOT.OTSecurity.OT.rand2_t * Sch.Scheme.rand_t.
  
   type msg1_t = SomeOT.msg1_t.
   type msg2_t = SomeOT.msg2_t.
   type msg3_t = SomeOT.msg3_t * Sch.Scheme.funG_t * Sch.Scheme.outputK_t * 
                 word array.
   type conv_t = msg1_t * msg2_t * msg3_t.
   
   op p1_stage1 (i1:bool array) (r1:rand1_t) (m1:msg1_t): state1_t * msg2_t  =
     SomeOT.msg2 i1 r1 m1.
   
   op p1_stage2 (st:state1_t) (m3:msg3_t): Sch.Scheme.output_t =
     let (ot_msg_in,fg_in,ko_in,x2g_in) = m3 in
     let ot_out = SomeOT.result st ot_msg_in in
     let outG = Sch.Scheme.evalG fg_in (ot_out || x2g_in) in
         Sch.Scheme.decode ko_in outG.

   op p2_stage1 (i2:Sch.Scheme.fun_t * bool array) (r2:rand2_t): state2_t * msg1_t = 
      let (fn,x2) = i2 in
      let (r_ot,r_s) = r2 in
      let (n,m,q,a,b) = fst fn in 
      let r_f = ES.Local.randFormat (n+q) m r_s in
      let fg = ES.Local.funG fn r_f in (* Not calling Scheme functions, for efficiency *)
      let ki = ES.Local.inputK fn r_f in  (* Not calling Scheme functions, for efficiency *)
      let ko = ES.Local.outputK fn r_f in  (* Not calling Scheme functions, for efficiency *)
      let x2g = Sch.Scheme.Input.encode 
                  (drop (n - size (snd i2)) ki) x2 in
      let (st_ot,m1) = SomeOT.msg1 
                  (take (n - size (snd i2)) ki) (fst r_ot) in
          ((st_ot,fg,ko,x2g,snd r_ot) , m1).

   op p2_stage2 (st:state2_t) (m2:msg2_t): msg3_t  = 
      let (st_ot,fg,ko,x2g,r_ot2) = st in
      let m3 = SomeOT.msg3 st_ot r_ot2 m2 in
          (m3,fg,ko,x2g).
end Concrete.
import Concrete.
import ES.ProjScheme.

(*extraction "SFE.ml_tmp" 
  op p1_stage1,
  op p1_stage2,
  op p2_stage1,
  op p2_stage2
  with
  theory Array = "EcIArray".*)

(*********************************
  Correctness and Security proofs
**********************************)

  (* summarises the concrete protocol *)
  op conc_prot (i1 :bool array) (r1:rand1_t)
               (i2:Sch.Scheme.fun_t * bool array) (r2:rand2_t) : conv_t* (Sch.Scheme.output_t * unit) =
    let (st2, m1) = p2_stage1 i2 r2 in
    let (st1, m2) = p1_stage1 i1 r1 m1 in
    let m3 = p2_stage2 st2 m2 in
    let outcome = p1_stage2 st1 m3 in
    ((m1, m2, m3), (outcome, ())).

  clone ProtSec.ProtSecurity with 
    type Protocol.rand1_t = rand1_t,
    type Protocol.input1_t = bool array,
    type Protocol.output1_t = Sch.Scheme.output_t,
    type Protocol.leak1_t = int,
    type Protocol.rand2_t = rand2_t,
    type Protocol.input2_t = Sch.Scheme.fun_t * bool array,
    type Protocol.output2_t = unit,
    op Protocol.f (i1: input1_t, i2: input2_t) =
         (Sch.Scheme.eval (fst i2) (i1 || snd i2), ()),
    type Protocol.leak2_t = Sch.Scheme.fun_t * int,
    type Protocol.conv_t = conv_t,
    op Protocol.validInputs(i1: input1_t, i2: input2_t) =
       let (fg,x2) = i2 in
       0 < size i1 <= SomeOT.max_size /\ Sch.Scheme.validInputs fg (i1||x2),
    pred Protocol.validRands(i1: input1_t, i2: input2_t, r1: rand1_t, r2: rand2_t) =
       let (fg,x2) = i2 in
       Sch.Scheme.validRand fg (snd r2),
    op Protocol.prot = conc_prot,
    op Protocol.phi1 = SomeOT.OTSecurity.OTPSec.Protocol.phi1,
    op Protocol.phi2 (i2:input2_t) = (sch_phi (fst i2), size (snd i2)).

  clone SFE.SFE as CSFE with
    type ProjScheme.token_t = W.word,
    (* Scheme *)
    type ProjScheme.Sch.Scheme.fun_t = ES.ProjScheme.Sch.Scheme.fun_t,
    type ProjScheme.Sch.Scheme.funG_t = ES.ProjScheme.Sch.Scheme.funG_t,
    type ProjScheme.Sch.Scheme.output_t = ES.ProjScheme.Sch.Scheme.output_t,
    type ProjScheme.Sch.Scheme.outputK_t = ES.ProjScheme.Sch.Scheme.outputK_t,
    type ProjScheme.Sch.Scheme.outputG_t = ES.ProjScheme.Sch.Scheme.outputG_t,
    type ProjScheme.Sch.Scheme.leak_t = ES.ProjScheme.Sch.Scheme.leak_t,
    type ProjScheme.Sch.Scheme.rand_t = ES.ProjScheme.Sch.Scheme.rand_t,
    pred ProjScheme.Sch.Scheme.validRand = ES.ProjScheme.Sch.Scheme.validRand,
    op ProjScheme.Sch.Scheme.validInputs = ES.ProjScheme.Sch.Scheme.validInputs,
    op ProjScheme.Sch.Scheme.phi = ES.ProjScheme.Sch.Scheme.phi,
    op ProjScheme.Sch.Scheme.eval = ES.ProjScheme.Sch.Scheme.eval,
    op ProjScheme.Sch.Scheme.funG = ES.ProjScheme.Sch.Scheme.funG,
    op ProjScheme.Sch.Scheme.inputK = ES.ProjScheme.Sch.Scheme.inputK,
    op ProjScheme.Sch.Scheme.outputK = ES.ProjScheme.Sch.Scheme.outputK,
    op ProjScheme.Sch.Scheme.decode = ES.ProjScheme.Sch.Scheme.decode,
    op ProjScheme.Sch.Scheme.evalG = ES.ProjScheme.Sch.Scheme.evalG,
    op ProjScheme.Sch.Scheme.pi_sampler = ES.ProjScheme.Sch.Scheme.pi_sampler,
    (* OT *)
    type ot_rand1_t = SomeOT.OTSecurity.OT.rand1_t,
    type ot_rand2_t = SomeOT.OTSecurity.OT.rand2_t,
    type ot_conv_t = SomeOT.OTSecurity.OT.conv_t,
    op ot_prot = SomeOT.OTSecurity.OT.prot,
    op sfe_sch_phi = sch_phi,
    op leakInterface = leakInterface,
    op OTSecurity.OT.max_size = SomeOT.OTSecurity.OT.max_size.
    
 (* Correctness *)

 lemma phi_sch_phi (fn: Sch.Scheme.fun_t) :
  Sch.Scheme.phi (sch_phi fn) = Sch.Scheme.phi fn.
 proof strict. rewrite /sch_phi; case pfe_or_sfe; smt. qed.

 lemma length_inputK fn r:
  let (n, m, q, aa, bb) = fst fn in
  0 < n =>
  0 <= q =>
  size (Sch.Scheme.inputK fn r) = n.
 proof strict. 
   simplify fst. 
   rewrite /Sch.Scheme.inputK /ES.Local.inputK /fst //.
   elim fn.`1 => n m q aa bb hn hq. simplify.
   
 rewrite /= size_sub //; first smt.
 rewrite /ES.Local.randFormat.
 cut Hr: size r < n + q
         \/ (size r < n +q)=false by smt.
 elim Hr => Hr; rewrite Hr //=.
 rewrite size_offun; smt. 
 rewrite size_mapi; smt.
 qed.

 lemma compatible :
  CSFE.Compatibility ().
 proof strict.
 delta CSFE.Compatibility CSFE.ProtSecurity.Protocol.validInputs => /= i1 i2 [H1].
  rewrite /CSFE.ProjScheme.Sch.Scheme.validInputs /Sch.Scheme.validInputs
          /Sch.Scheme.validInputs /ES.Local.validInputs.
  elim i2=> fn2 xx2 /=.
  elim fn2=> tt2 gg2 /=.
  elim tt2=> n m q aa bb /=.
  rewrite /ES.Local.validCircuit.
  simplify fst snd.
  rewrite size_append => /= [[H2] [H3 H4]].
  split; rewrite /CSFE.leakInterface /leakInterface
     /CSFE.ProtSecurity.Protocol.phi2 /CSFE.sfe_sch_phi !/fst !/snd /=; first smt.
  split;simplify delta.
    by case pfe_or_sfe; smt.
    move=> r; case (size r < n + q)=> lenr_nq.
      rewrite size_sub //=; first smt.
      by rewrite size_mkarray; smt.
      rewrite size_sub //=; first smt.
      by rewrite size_mapi; smt.
 qed.

 (* bijection between concrete and abstract PFE/SFE protocol views *) 
 op conv_trl (sfe_conv:CSFE.ProtSecurity.Protocol.conv_t)
 : ProtSecurity.Protocol.conv_t =
  let (fg,x2g,oK) = fst sfe_conv in
  let (otm1,otm2,otm3) =  snd sfe_conv in
  (otm1,otm2,(otm3,fg,oK,x2g)).

 lemma prot_trl: forall i1 r1 i2 r2,
  CSFE.ProtSecurity.Protocol.validInputs i1 i2 =>
  (*let r2' = (let (r21, r22) = r2 in let (n, m, q, aa, bb) = fst (fst i2) in (r21, ES.Local.randFormat (n + q)%Int m r22)) in*)
  ProtSecurity.Protocol.prot i1 r1 i2 r2
  = ( conv_trl (fst (CSFE.ProtSecurity.Protocol.prot i1 r1 i2 r2))
    , snd (CSFE.ProtSecurity.Protocol.prot i1 r1 i2 r2)).
 proof strict. 
move => i1 r1 i2 r2.
   elim r2=> r21 r22 /=.
   elim i2=> fn x /=.
   elim fn=> topo gg /=.
   elim topo=> n m q aa bb /=.
   move => Hvalid.
   cut Hcompat: CSFE.Compatibility () by apply compatible.
   move : Hcompat; rewrite /CSFE.Compatibility => Hcompat.
   elim (Hcompat i1 (((n,m,q,aa,bb),gg),x) _); first smt.
   move=> {Hcompat} Hleak1 [Hleak2] HlenIK.
   move : Hvalid;
   rewrite /CSFE.ProtSecurity.Protocol.validInputs /CSFE.ProtSecurity.Protocol.validInputs
    /CSFE.ProjScheme.Sch.Scheme.validInputs /Sch.Scheme.validInputs /Sch.Scheme.validInputs /Sch.Scheme.validInputs /ES.Local.validInputs size_append /=
    => [[H1] [H2 H3]].
   rewrite /ProtSecurity.Protocol.prot /conc_prot.
   rewrite /conc_prot /p2_stage1 /p2_stage2 /p1_stage1 /p1_stage2.
   rewrite /CSFE.ProtSecurity.Protocol.prot /CSFE.ProtSecurity.Protocol.prot
    /CSFE.OTSecurity.OT.prot /SomeOT.OTSecurity.OT.prot /SomeOT.ot_prot /=
    /CSFE.OTSecurity.OTPSec.Protocol.prot /CSFE.OTSecurity.OT.prot
    /CSFE.OTSecurity.OT.prot /CSFE.ot_prot /SomeOT.OTSecurity.OT.prot /SomeOT.ot_prot ! fst_pair ! snd_pair /=.
   pose sm1 := (SomeOT.msg1 _ _); rewrite (pairS sm1) /=.
   pose sm2 := (SomeOT.msg2 _ _ _); rewrite (pairS sm2) /=.
   pose sm3 := (SomeOT.msg3 _ _ _); rewrite (pairS sm3) /=.
   pose sm1' := (SomeOT.msg1 _ _); rewrite (pairS sm1') /=.
   pose sm2' := (SomeOT.msg2 _ _ _); rewrite (pairS sm2') /=.
   pose sm3' := (SomeOT.msg3 _ _ _); rewrite (pairS sm3') /=.
   cut -> : sm1 = sm1' by smt.
   cut -> : sm2 = sm2' by smt.
   cut -> : sm3 = sm3' by smt.
   cut ->: (CSFE.ProjScheme.Sch.Scheme.decode = Sch.Scheme.decode) by trivial.
 cut ->: (CSFE.ProjScheme.Sch.Scheme.evalG = Sch.Scheme.evalG) by trivial.
 cut ->: (CSFE.ProjScheme.Sch.Scheme.Input.encode = Sch.Scheme.Input.encode) by trivial.
 cut ->: (CSFE.ProjScheme.Sch.Scheme.funG = Sch.Scheme.funG) by trivial.
 cut ->: (CSFE.ProjScheme.Sch.Scheme.outputK = Sch.Scheme.outputK) by trivial.
 cut ->: (CSFE.ProjScheme.Sch.Scheme.inputK = Sch.Scheme.inputK) by trivial.
 cut -> : n - size x = size i1 by smt.
 do ! (split=> //).
 qed.
 
 lemma Correctness: 
  ProtSecurity.Correct ().
 proof.
 cut: ES.SomeDKC.PrfDKC.Correct () by rewrite ES.SomeDKC.PrfDKC_correct. 
 move => DKCh. 
 rewrite /ProtSecurity.Correct /ProtSecurity.Protocol.validInputs=> i1 r1 i2 r2.

   rewrite (pairS i2) /= => [H1 H2]. 

   rewrite prot_trl /CSFE.ProtSecurity.Protocol.validInputs
    /CSFE.ProtSecurity.Protocol.validInputs /CSFE.ProjScheme.Sch.Scheme.validInputs /Sch.Scheme.validInputs !snd_pair ?fst_pair.
   by smt. 
  cut ->: ProtSecurity.Protocol.f = CSFE.ProtSecurity.Protocol.f by trivial.
  apply CSFE.PFE_Correctness.
   by apply compatible. 
   rewrite ES.sch_correct.
   by apply SomeOT.ot_correct.
   by smt.
   move : H2.
   simplify ProtSecurity.Protocol.validRands CSFE.ProtSecurity.Protocol.validRands CSFE.ProtSecurity.Protocol.validRands CSFE.ProjScheme.Sch.Scheme.validRand Sch.Scheme.validRand ES.ProjScheme.Sch.Scheme.validRand.
   by rewrite !/fst /=.
 qed.

 (* Security *)

 module R1 = CSFE.PFE_R1(SomeOT.R1).
 print CSFE.PFE_R2.
 print ES.SomeGarble.Rand.
 print ES.SomeGarble.tokens_t.
 
 print CSFE.SchSecurity.EncSecurity.Encryption.rand.
 print CSFE.ProjScheme.Sch.Scheme.rand_t.
 print Sch.Scheme.rand_t.


 module R2 = CSFE.PFE_R2(SomeOT.R2, ES.Rand). 
 module SFESim = CSFE.PFE_S(ES.Rand,ES.SchSecurity.EncSecurity.SIM(ES.Rand),SomeOT.S).

 module S : ProtSecurity.Sim_t = {
  proc sim1(i1 : ProtSecurity.Protocol.input1_t,
           o1 : ProtSecurity.Protocol.output1_t,
           l2 : ProtSecurity.Protocol.leak2_t) : ProtSecurity.view1_t = {
   var sfe_view : CSFE.ProtSecurity.view1_t;
     
   sfe_view = SFESim.sim1(i1,o1,l2);
   return (fst sfe_view,conv_trl (snd sfe_view));
  }

  proc sim2(i2 : ProtSecurity.Protocol.input2_t,
           o2 : ProtSecurity.Protocol.output2_t,
           l1 : ProtSecurity.Protocol.leak1_t) : ProtSecurity.view2_t = {
   var sfe_view : CSFE.ProtSecurity.view2_t;

   sfe_view = SFESim.sim2(i2,o2,l1);
   return (fst sfe_view,conv_trl (snd sfe_view));
  }
 }.

 module SFE_A1(A1 : ProtSecurity.Adv1_t) : CSFE.ProtSecurity.Adv1_t = {
  proc gen_query()
  : CSFE.ProtSecurity.Protocol.input1_t*CSFE.ProtSecurity.Protocol.input2_t = {
   var query: ProtSecurity.Protocol.input1_t*ProtSecurity.Protocol.input2_t;
   query =  A1.gen_query();
   return query;
  }

  proc dist (view: CSFE.ProtSecurity.view1_t) : bool = {
   var guess: bool;
   guess = A1.dist((fst view, conv_trl(snd view)));
   return guess;
  }        
 }.

 module SFE_A2(A2 : ProtSecurity.Adv2_t) : CSFE.ProtSecurity.Adv2_t = {
  proc gen_query()
  : CSFE.ProtSecurity.Protocol.input1_t*CSFE.ProtSecurity.Protocol.input2_t={
   var query: ProtSecurity.Protocol.input1_t*ProtSecurity.Protocol.input2_t;
   query =  A2.gen_query();
   return query;
  }
  proc dist (view: CSFE.ProtSecurity.view2_t) : bool = {
   var guess: bool;
   guess = A2.dist((fst view, conv_trl(snd view)));
   return guess;
  }
 }.

 lemma Connect_SFE_1 : 
  forall (A1 <: ProtSecurity.Adv1_t) &m,
   islossless A1.gen_query =>
   islossless A1.dist =>
   equiv [ ProtSecurity.Game1(R1, R2, S, A1).main ~
           CSFE.ProtSecurity.Game1(R1, R2, SFESim, SFE_A1(A1)).main : 
          ={glob A1} ==> ={res} ].
 proof strict.
 move => A1 &m A1genll A1distll; proc.
 inline ProtSecurity.Game1(CSFE.PFE_R1(SomeOT.R1),CSFE.PFE_R2(SomeOT.R2,ES.Rand),S,A1).game.
 inline CSFE.ProtSecurity.Game1(CSFE.PFE_R1(SomeOT.R1),CSFE.PFE_R2(SomeOT.R2,ES.Rand),CSFE.PFE_S(ES.Rand,ES.SchSecurity.EncSecurity.SIM(ES.Rand),SomeOT.S),SFE_A1(A1)).game.
 seq 3 3 : (={i1, i2, b, glob A1} /\ real{1} = real{2}).
  inline SFE_A1(A1).gen_query. 
  by wp; call (_: true); wp; rnd.
 if.
   move=> &1 &2 [[->>] [->>] eqA] eqr.
   elim (i2{2})=> fg x2.
   rewrite /CSFE.ProtSecurity.Protocol.validInputs /fst /snd /=.
   rewrite /ProtSecurity.Protocol.validInputs /=.
   by rewrite /CSFE.ProjScheme.Sch.Scheme.validInputs.
   by auto.
 if=> //.
  inline SFE_A1(A1).dist.
  wp; call (_:  true).
  wp; call (_: ={i2info} ==> ={res}).
   by proc; call ES.Rand_stateless; call SomeOT.R2_stateless.
  call (_ : ={i1info} ==> ={res}).
   by proc; call SomeOT.R1_stateless.
  skip;progress;
  by rewrite snd_pair prot_trl; move : H; 
     rewrite /ProtSecurity.Protocol.validInputs
             /CSFE.ProtSecurity.Protocol.validInputs
             /CSFE.ProjScheme.Sch.Scheme.validInputs;
     elim (i2{2}).
 inline SFE_A1(A1).dist.
 wp; call (_: true).
 inline S.sim1 SFESim.sim1.
 inline CSFE.PFE_S(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), SomeOT.S).sim1.
 wp; call SomeOT.S1_stateless; call ES.Sim_stateless.
 by auto.
 qed.

 lemma Connect_SFE_1_pr : 
  forall (A1 <: ProtSecurity.Adv1_t) &m,
   islossless A1.gen_query =>
   islossless A1.dist =>
   Pr[ProtSecurity.Game1(R1, R2, S, A1).main() @ &m : res] = 
   Pr[CSFE.ProtSecurity.Game1(R1, R2, SFESim, SFE_A1(A1)).main() @ &m : res].
 proof strict.
 move => A1 &m A1genll A1getll.
 byequiv (Connect_SFE_1 A1 &m _ _) => //.
 qed.

 lemma Connect_SFE_2 : 
  forall (A2 <: ProtSecurity.Adv2_t) &m,
    islossless A2.gen_query =>
    islossless A2.dist =>
    equiv [ ProtSecurity.Game2(R1, R2, S, A2).main ~
            CSFE.ProtSecurity.Game2(R1, R2, SFESim, SFE_A2(A2)).main : 
            ={glob A2} ==> ={res} ].
 proof strict.
 move => A2 &m A2genll A2getll; proc.
 inline ProtSecurity.Game2(CSFE.PFE_R1(SomeOT.R1),CSFE.PFE_R2(SomeOT.R2,ES.Rand),S,A2).game.
 inline CSFE.ProtSecurity.Game2(CSFE.PFE_R1(SomeOT.R1),CSFE.PFE_R2(SomeOT.R2,ES.Rand),CSFE.PFE_S(ES.Rand,ES.SchSecurity.EncSecurity.SIM(ES.Rand),SomeOT.S),SFE_A2(A2)).game.
 seq 3 3: (={glob A2,i1,i2,b} /\ real{1} = real{2}).
  inline SFE_A2(A2).gen_query.
  wp; call (_: true).
  by auto.
 if.
  move=> &1 &2 [[eqA]] [->>] [->>] eqb eqr.
  elim (i2{2})=> fg x2.
  rewrite /CSFE.ProtSecurity.Protocol.validInputs /fst /snd /=.
  rewrite /ProtSecurity.Protocol.validInputs /=.
  by rewrite /CSFE.ProjScheme.Sch.Scheme.validInputs.
  by auto.
 if=> //.
   inline SFE_A2(A2).dist.
   wp; call (_: true).
   wp; inline CSFE.PFE_R2(SomeOT.R2, ES.Rand).gen.
   wp; call ES.Rand_stateless; call SomeOT.R2_stateless.
   wp; inline CSFE.PFE_R1(SomeOT.R1).gen.
   wp; call (_ : ={i1info} ==> ={res}); first by proc; rnd; wp; skip.
   by wp; skip; progress;
      rewrite snd_pair prot_trl; move : H;
      rewrite /ProtSecurity.Protocol.validInputs
              /CSFE.ProtSecurity.Protocol.validInputs
              /CSFE.ProjScheme.Sch.Scheme.validInputs;
      elim (i2{2}).
  inline SFE_A2(A2).dist.
  wp;call (_: true).
  inline S.sim2 SFESim.sim2.
  inline CSFE.PFE_S(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), SomeOT.S).sim2.
  wp; call SomeOT.S2_stateless; call ES.Rand_stateless.
  by auto.
 qed.

 lemma Connect_SFE_2_pr : 
  forall (A2 <: ProtSecurity.Adv2_t) &m,
    islossless A2.gen_query =>
    islossless A2.dist =>
     Pr[ProtSecurity.Game2(R1, R2, S, A2).main() @ &m : res] = 
       Pr[CSFE.ProtSecurity.Game2(R1, R2, SFESim, SFE_A2(A2)).main() @ &m : res].
 proof strict.
 move => A2 &m A2genll A2getll.
 by byequiv (Connect_SFE_2 A2 &m _ _).
 qed.

 lemma Connect_SomeOT_1 : 
  forall (A1 <: CSFE.OTSecurity.OTPSec.Adv1_t) &m,
    islossless A1.gen_query =>
    islossless A1.dist =>
    equiv [ CSFE.OTSecurity.OTPSec.Game1(SomeOT.R1, SomeOT.R2, SomeOT.S, A1).main ~
            SomeOT.OTSecurity.OTPSec.Game1(SomeOT.R1, SomeOT.R2, SomeOT.S, A1).main : 
            ={glob A1} ==> ={res} ].
 proof strict.
 move => A1 &m A1genll A1distll; proc.
  inline CSFE.OTSecurity.OTPSec.Game1(SomeOT.R1,SomeOT.R2,SomeOT.S,A1).game.
 inline SomeOT.OTSecurity.OTPSec.Game1(SomeOT.R1,SomeOT.R2,SomeOT.S,A1).game.
 seq 3 3 : (={i1,i2,b,glob A1} /\ real{1} = real{2}).
  by call (_: true); auto.
 if=> //; first by smt. by auto.
 if=> //.
   wp; call (_: true).
   by wp; call SomeOT.R2_stateless; call SomeOT.R1_stateless.
  wp; call (_: true).
  wp; call SomeOT.S1_stateless.
  by auto.
 qed.

 lemma Connect_SomeOT_1_pr : 
  forall (A1 <: CSFE.OTSecurity.OTPSec.Adv1_t) &m,
   islossless A1.gen_query =>
   islossless A1.dist =>
   Pr[CSFE.OTSecurity.OTPSec.Game1(SomeOT.R1, SomeOT.R2, SomeOT.S, A1).main() @ &m : res] =
   Pr[SomeOT.OTSecurity.OTPSec.Game1(SomeOT.R1, SomeOT.R2, SomeOT.S, A1).main() @ &m : res].
 proof strict.
 move => A1 &m A1genll A1getll.
 by byequiv (Connect_SomeOT_1 A1 &m _ _).
 qed.

 lemma Connect_SomeOT_2 : 
  forall (A2 <: CSFE.OTSecurity.OTPSec.Adv2_t) &m,
   islossless A2.gen_query =>
   islossless A2.dist =>
   equiv [ CSFE.OTSecurity.OTPSec.Game2(SomeOT.R1, SomeOT.R2, SomeOT.S, A2).main ~
           SomeOT.OTSecurity.OTPSec.Game2(SomeOT.R1, SomeOT.R2, SomeOT.S, A2).main : 
           ={glob A2} ==> ={res} ].
 proof strict.
 move => A2 &m A2genll A2distll; proc.
 inline CSFE.OTSecurity.OTPSec.Game2(SomeOT.R1,SomeOT.R2,SomeOT.S,A2).game.
 inline SomeOT.OTSecurity.OTPSec.Game2(SomeOT.R1,SomeOT.R2,SomeOT.S,A2).game.
 seq 3 3: (={i1,i2,b,glob A2} /\ real{1} = real{2} ).
  by call (_: true); auto.
 if=> //; first by smt. by auto. 
 if=> //.
   wp; call (_: true).
   by wp; call SomeOT.R2_stateless; call SomeOT.R1_stateless.
  wp; call (_: true).
  by wp; call SomeOT.S2_stateless; auto.
 qed.

 lemma Connect_SomeOT_2_pr : 
  forall (A2 <: CSFE.OTSecurity.OTPSec.Adv2_t) &m,
    islossless A2.gen_query =>
    islossless A2.dist =>
     Pr[CSFE.OTSecurity.OTPSec.Game2(SomeOT.R1, SomeOT.R2, SomeOT.S, A2).main() @ &m : res] = Pr[SomeOT.OTSecurity.OTPSec.Game2(SomeOT.R1, SomeOT.R2, SomeOT.S, A2).main() @ &m : res].
 proof strict.
 move => A2 &m A2genll A2getll.
 by byequiv (Connect_SomeOT_2 A2 &m _ _).
 qed.

 lemma Connect_SomeGarble : 
  forall (A <: CSFE.SchSecurity.EncSecurity.Adv_SIM_t) &m,
   islossless A.gen_query =>
   islossless A.get_challenge =>
   equiv [ CSFE.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), A).main ~
           ES.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), A).main :
           ={glob A} ==> ={res}  ].
 proof strict.
 move => A &m Agenll Agetll; proc.
 inline CSFE.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), A).game.
 inline ES.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), A).game.
   wp; seq 3 3 : (={glob A,query, b} /\ real{1} = real{2} /\ b{1} = real{1}).
  call (_ : ={glob A} ==> ={glob A,res}); first by proc true.
  wp;rnd. by skip.
 case (CSFE.SchSecurity.EncSecurity.queryValid_SIM query{1}).
  rcondf {1} 1; first by move =>  &m0; skip.
  rcondf {2} 1; first by move =>  &m0; skip; smt.
  case (real{1}).
   rcondt {1} 1; first by move =>  &m0; skip.
   rcondt {2} 1; first by move =>  &m0; skip.
   call (_ : ={glob A,cipher} ==> ={res,glob A}); first by proc true.
   wp; call ES.Rand_stateless.
   skip;progress;smt.
  rcondf {1} 1; first by move =>  &m0; skip.
  rcondf {2} 1; first by move =>  &m0; skip.
  call (_ : ={glob A,cipher} ==> ={res,glob A}); first by proc true.
  inline ES.SchSecurity.EncSecurity.SIM(ES.Rand).simm.
  wp; call ES.Rand_stateless.
  wp;skip;progress;smt.
 rcondt {1} 1; first by move =>  &m0; skip.
 rcondt {2} 1; first by move =>  &m0; skip; smt.
 rnd;wp;skip;smt.
 qed.

 lemma Connect_SomeGarble_pr : 
  forall (A <: CSFE.SchSecurity.EncSecurity.Adv_SIM_t) &m,
   islossless A.gen_query =>
   islossless A.get_challenge =>
   Pr[CSFE.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), A).main() @ &m : res ] =
   Pr[ES.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), A).main() @ &m : res].
 proof strict.
 move => A &m Agenll Agetll.
 by byequiv (Connect_SomeGarble A &m _ _).
 qed.

 print SomeOT.ot_correct.
 
 lemma Connect_SFE : 
 forall (PFE_A1<:CSFE.ProtSecurity.Adv1_t {SomeOT.R1, SomeOT.R2, SomeOT.S,ES.Rand, ES.SchSecurity.EncSecurity.SIM, CSFE.B_OT1, CSFE.B_G})
        (PFE_A2<:CSFE.ProtSecurity.Adv2_t{SomeOT.R1, SomeOT.R2, SomeOT.S,ES.Rand, ES.SchSecurity.EncSecurity.SIM, CSFE.B_OT2, CSFE.B_G}) &m, 
  islossless PFE_A1.gen_query => islossless PFE_A1.dist =>
  islossless PFE_A2.gen_query => islossless PFE_A2.dist =>
   `|2%r * Pr[CSFE.ProtSecurity.Game1(R1, R2, SFESim, PFE_A1).main()@ &m:res] - 1%r| <=
     `|2%r * Pr[CSFE.OTSecurity.OTPSec.Game1(SomeOT.R1, SomeOT.R2, SomeOT.S, CSFE.B_OT1(ES.Rand, PFE_A1)).main() @ &m : res] - 1%r| +
     `|2%r * Pr[CSFE.SchSecurity.EncSecurity.Game_SIM(ES.Rand, ES.SchSecurity.EncSecurity.SIM(ES.Rand), CSFE.B_G(SomeOT.S, PFE_A1)).main() @ &m : res] - 1%r| /\
   `|2%r * Pr[CSFE.ProtSecurity.Game2(R1, R2, SFESim, PFE_A2).main()@ &m:res] - 1%r| <=
     `|2%r * Pr[CSFE.OTSecurity.OTPSec.Game2(SomeOT.R1, SomeOT.R2, SomeOT.S, CSFE.B_OT2(ES.Rand, PFE_A2)).main() @ &m : res] - 1%r|.   
 proof strict.
move => A1 A2 &m A1_gen_ll A1_dist_ll A2_gen_ll A2_dist_ll.
apply (CSFE.PFE_Security _ _ SomeOT.R1 SomeOT.R2 SomeOT.S ES.Rand (ES.SchSecurity.EncSecurity.SIM(ES.Rand)) A1 A2 &m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); trivial.
 by apply compatible; smt.
 by apply SomeOT.ot_correct.
 by apply SomeOT.R1_lossless.
 by apply SomeOT.R2_lossless.
 by apply SomeOT.S1_lossless.
 by apply SomeOT.S2_lossless.
 by apply ES.Rand_islossless.
 by proc; wp; call ES.Rand_islossless; wp.
qed.

require import OldMonoid.
require import Sum.
require import FSet.
require import Real.
require import Bool.
require import NewFMap.
require import Option.

import ES.
import SG.
import Tweak.
import W.

print ES.SG.DKCSecurity.

lemma prf_reduction eps_prf (A <: ES.SG.Sec.EncSecurity.Adv_IND_t{ES.SG.Rand,ES.SG.R,ES.SG.C,ES.SG.DKC_Adv,ES.SG.DKCSecurity.DKCp,ES.SG.DKCSecurity.DKC_O,ES.SomeDKC.PRF.PRFr_Wrapped,ES.SomeDKC.PRF.RandomFunction,ES.SomeDKC.DKCSecurity.DKCp,ES.SomeDKC.Param}) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
    (forall i, 0 <= i < ES.bound => (Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.PRFr_Wrapped,ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main(i)@ &m:res] - Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.RandomFunction,ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main(i)@ &m:res]) <= eps_prf) =>
    
  Pr[ES.SG.GameReal(A).garble() @ &m : res] - Pr[ES.SG.GameFake(A).garble() @ &m : res] <= ES.bound%r * eps_prf.
proof.
  move => Agen_ll Aget_ll prf_eps.
  cut ->: Pr[ES.SG.GameReal(A).garble() @ &m : res] = Pr[ES.SG.GameHybrid(A).garble(-1) @ &m : res].
    by byequiv (ES.SG.GameReal_GameHybrid0 A Agen_ll Aget_ll). 
  cut ->: Pr[ES.SG.GameFake(A).garble() @ &m : res] = Pr[ES.SG.GameHybrid(A).garble(ES.bound - 1) @ &m : res].
    by byequiv (ES.SG.GameFake_GameHybridBound A _ _).
  rewrite (ES.SG.reductionSimplified A &m _ _) //.
  cut ->: ES.SG.bound = ES.bound by idtac=>/#.
  cut ->: Mrplus.sum
   (fun (i0 : int) =>
      Pr[ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game
         (true, i0) @ &m : res] -
      Pr[ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game
         (false, i0) @ &m : !res]) (intval 0 (ES.bound - 1)) = Mrplus.sum 
     (fun (i0 : int) =>
       Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.PRFr_Wrapped,ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main(i0)@ &m:res] -
       Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.RandomFunction,ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main(i0)@ &m:res]) (intval 0 (ES.bound - 1)).
     rewrite (Mrplus.sum_eq (fun (i0 : int) =>
      Pr[ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game
         (true, i0) @ &m : res] -
      Pr[ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game
         (false, i0) @ &m : !res]) (fun (i0 : int) =>
      Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.PRFr_Wrapped, ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main
         (i0) @ &m : res] -
      Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.RandomFunction, ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main
        (i0) @ &m : res])).
           move => x. rewrite intval_def => [[?]] ?. 
          simplify.  congr. 
          cut ->: Pr[ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game (true, x) @ &m : res] = Pr[ES.SomeDKC.DKCSecurity.Game(ES.SomeDKC.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game (true, x) @ &m : res].  

  byequiv. 
  proc => //.
  
          inline ES.SG.DKCSecurity.DKC_O.initialize ES.SomeDKC.DKCSecurity.DKC_O.initialize.
  
  seq 8 8 : (={l,b,glob A,b0,l0} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ l{2} = x /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2}). auto; progress. 

  seq 3 3 : (={l,b,glob A,b0,l0,lsb} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ l{2} = x /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ SomeDKC.DKCSecurity.DKCp.lsb{2} = lsb{2} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2}).

  wp.
  
  while (={l,b,glob A,b0,l0,i} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l{2} = x /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2}).
          if. auto. auto. auto. auto. 

  inline ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).A.get_challenge ES.SomeDKC.DKCSecurity.Game(ES.SomeDKC.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).A.get_challenge.

  seq 3 3 : (={l,b,glob A,b0,l0,lsb0,l1,query_ind} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ SomeDKC.DKCSecurity.DKCp.lsb{2} = lsb{2} /\ lsb0{2} = lsb{2} /\ l{2} = x /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2}).
          call (_ : true). auto. 

  
  if. auto. 

          seq 3 3 : ((={l,b,glob A,b0,l0,lsb0,l1,query_ind} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ SomeDKC.DKCSecurity.DKCp.lsb{2} = lsb{2} /\ lsb0{2} = lsb{2} /\ l{2} = x /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2})
    /\
    (={glob A,real,p}) /\ ={glob ES.SG.C} /\
      size ES.SG.C.v{1} = (ES.SG.C.n + ES.SG.C.q){1} /\
      ES.SG.C.f{1} = ((ES.SG.C.n, ES.SG.C.m, ES.SG.C.q, ES.SG.C.aa, ES.SG.C.bb), ES.SG.C.gg){1} /\
      ES.SG.validInputsP (ES.SG.C.f, ES.SG.C.x){1} /\
      (forall i, 0 <= i < ES.SG.C.n{2} => ES.SG.C.v{2}.[i] = ES.SG.C.x{2}.[i]) /\
      (forall i, ES.SG.C.n <= i < ES.SG.C.n + ES.SG.C.q => ES.SG.C.v{2}.[i] = oget ES.SG.C.gg.[(i, ES.SG.C.v{2}.[ES.SG.C.aa{2}.[i]], ES.SG.C.v{2}.[ES.SG.C.bb.[i]])]){2}).
      call ES.SG.CircuitInitEquiv'.
      auto; progress. 
        by move : H3; rewrite /queryValid_IND /valid_plain /validInputs /validInputsP ?ES.SG.valid_wireinput /valid_circuitP /fst /snd; case realL. 

          wp. call (_ : true). wp. 

    inline AdvInit(DKCSecurity.DKC_O).init AdvInit(SomeDKC.DKCSecurity.DKC_O).init.
    
    seq 8 8 : ((={l,b,glob A,b0,l0,lsb0,l1,query_ind} /\ ={glob R, useVisible,lsb1,l2} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ l2{1} = l1{1} /\ useVisible{1} /\ R.t{2}.[SomeDKC.DKCSecurity.DKCp.l{2}] = !SomeDKC.DKCSecurity.DKCp.lsb{2} /\ lsb0{2} = SomeDKC.DKCSecurity.DKCp.lsb{2} /\ SomeDKC.DKCSecurity.DKCp.lsb{2} = lsb{2} /\ lsb0{2} = lsb{2} /\ l{2} = x /\ size R.t{2} = C.n{2} + C.q{2} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2})
    /\
    (={glob A,real,p}) /\ ={glob ES.SG.C} /\
      size ES.SG.C.v{1} = (ES.SG.C.n + ES.SG.C.q){1} /\
      ES.SG.C.f{1} = ((ES.SG.C.n, ES.SG.C.m, ES.SG.C.q, ES.SG.C.aa, ES.SG.C.bb), ES.SG.C.gg){1} /\
      ES.SG.validInputsP (ES.SG.C.f, ES.SG.C.x){1} /\
      (forall i, 0 <= i < ES.SG.C.n{2} => ES.SG.C.v{2}.[i] = ES.SG.C.x{2}.[i]) /\
      (forall i, ES.SG.C.n <= i < ES.SG.C.n + ES.SG.C.q => ES.SG.C.v{2}.[i] = oget ES.SG.C.gg.[(i, ES.SG.C.v{2}.[ES.SG.C.aa{2}.[i]], ES.SG.C.v{2}.[ES.SG.C.bb.[i]])]){2}).

    wp. 
    while ((={l,b,glob A,b0,l0,lsb0,l1,query_ind,i1} /\ ={glob R, useVisible,lsb1,l2} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = fset0 /\ lsb0{2} = SomeDKC.DKCSecurity.DKCp.lsb{2} /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ l2{1} = l1{1} /\ useVisible{1} /\ SomeDKC.DKCSecurity.DKCp.lsb{2} = lsb{2} /\ lsb0{2} = lsb{2} /\ l{2} = x /\ size R.t{2} = C.n{2} + C.q{2} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2})
    /\
    (={glob A,real,p}) /\ ={glob ES.SG.C} /\
      size ES.SG.C.v{1} = (ES.SG.C.n + ES.SG.C.q){1} /\
      ES.SG.C.f{1} = ((ES.SG.C.n, ES.SG.C.m, ES.SG.C.q, ES.SG.C.aa, ES.SG.C.bb), ES.SG.C.gg){1} /\
      ES.SG.validInputsP (ES.SG.C.f, ES.SG.C.x){1} /\
      (forall i, 0 <= i < ES.SG.C.n{2} => ES.SG.C.v{2}.[i] = ES.SG.C.x{2}.[i]) /\
      (forall i, ES.SG.C.n <= i < ES.SG.C.n + ES.SG.C.q => ES.SG.C.v{2}.[i] = oget ES.SG.C.gg.[(i, ES.SG.C.v{2}.[ES.SG.C.aa{2}.[i]], ES.SG.C.v{2}.[ES.SG.C.bb.[i]])]){2}).

        auto. progress. rewrite size_set. done. auto. progress. rewrite size_offun max_ler => /#. rewrite get_set => /#. rewrite size_set. done. 

    inline AdvInit(DKCSecurity.DKC_O).garble AdvInit(SomeDKC.DKCSecurity.DKC_O).garble.
    
    seq 8 8 : ((={l,b,glob A,b0,l0,lsb0,l1,query_ind} /\ ={glob R, useVisible,lsb1,l2} /\ ={glob G,l3} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ ES.SG.DKCSecurity.DKCp.used{1} = ES.SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ l2{1} = l1{1} /\ useVisible{1} /\ l3{1} = l1{1} /\ l{2} = x /\ size R.t{2} = C.n{2} + C.q{2} /\ R.t{2}.[SomeDKC.DKCSecurity.DKCp.l{2}] = !SomeDKC.DKCSecurity.DKCp.lsb{2} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2})
    /\
    (={glob A,real,p}) /\ ={glob ES.SG.C} /\
      size ES.SG.C.v{1} = (ES.SG.C.n + ES.SG.C.q){1} /\
      ES.SG.C.f{1} = ((ES.SG.C.n, ES.SG.C.m, ES.SG.C.q, ES.SG.C.aa, ES.SG.C.bb), ES.SG.C.gg){1} /\
      ES.SG.validInputsP (ES.SG.C.f, ES.SG.C.x){1} /\
      (forall i, 0 <= i < ES.SG.C.n{2} => ES.SG.C.v{2}.[i] = ES.SG.C.x{2}.[i]) /\
      (forall i, ES.SG.C.n <= i < ES.SG.C.n + ES.SG.C.q => ES.SG.C.v{2}.[i] = oget ES.SG.C.gg.[(i, ES.SG.C.v{2}.[ES.SG.C.aa{2}.[i]], ES.SG.C.v{2}.[ES.SG.C.bb.[i]])]){2} /\

      (forall k, G.g{1} <= k <= C.n{1} + C.q{1} => !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true)))  /\
  (forall k, 0 <= k < C.n{1} => !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k C.x{2}.[k] R.t{2}.[0]))
    ).

    while ((={l,b,glob A,b0,l0,lsb0,l1,query_ind} /\ ={glob R, useVisible,lsb1,l2} /\ ={glob G,l3} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ DKCSecurity.DKCp.used{1} = SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ l2{1} = l1{1} /\ useVisible{1} /\ l3{1} = l1{1} /\ l{2} = x /\ size R.t{2} = C.n{2} + C.q{2} /\ R.t{2}.[SomeDKC.DKCSecurity.DKCp.l{2}] = !SomeDKC.DKCSecurity.DKCp.lsb{2} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2})
    /\
    (={glob A,real,p}) /\ ={glob ES.SG.C} /\
      size ES.SG.C.v{1} = (ES.SG.C.n + ES.SG.C.q){1} /\
      ES.SG.C.f{1} = ((ES.SG.C.n, ES.SG.C.m, ES.SG.C.q, ES.SG.C.aa, ES.SG.C.bb), ES.SG.C.gg){1} /\
      ES.SG.validInputsP (ES.SG.C.f, ES.SG.C.x){1} /\
      (forall i, 0 <= i < ES.SG.C.n{2} => ES.SG.C.v{2}.[i] = ES.SG.C.x{2}.[i]) /\
      (forall i, ES.SG.C.n <= i < ES.SG.C.n + ES.SG.C.q => ES.SG.C.v{2}.[i] = oget ES.SG.C.gg.[(i, ES.SG.C.v{2}.[ES.SG.C.aa{2}.[i]], ES.SG.C.v{2}.[ES.SG.C.bb.[i]])]){2} /\

      (*(forall k, C.n{1} <= k < G.g{1} => mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\*)
      
        C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      
  (forall k, G.g{1} <= k <= C.n{1} + C.q{1} => !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true)))  /\
  (forall k, 0 <= k < C.n{1} => !mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k C.x{2}.[k] R.t{2}.[0]))
      
    ).
        case (!C.aa{2}.[G.g{2}] <= l3{2}).
  rcondt{2} 3. auto. progress =>/#.
  rcondt{1} 3. auto. progress =>/#.

    inline*.

    rcondt{2} 10. progress. auto. progress. by idtac=>/#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#.

        rcondf{2} 15. auto. progress. idtac=>/#. 

        rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (Tweak.tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: Tweak.tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   Tweak.tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite W.from_int_inj_fun => /#. done. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 30. auto; progress. idtac=>/#. 
    rcondt{2} 40. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (Tweak.tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: Tweak.tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite W.from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite W.from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 45. auto; progress. cut ->: l{hr} = C.aa{hr}.[G.g{hr}] <=> false by idtac=> /#. cut ->: l{hr} = C.bb{hr}.[G.g{hr}] <=> false by idtac=>/#. by simplify.
     rcondt{2} 55. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 60. auto; progress. cut ->: l{hr} = C.aa{hr}.[G.g{hr}] <=> false by idtac=> /#. cut ->: l{hr} = C.bb{hr}.[G.g{hr}] <=> false by idtac=>/#. by simplify. 


     rcondt{1} 10. progress. auto. progress. by idtac=>/#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#.

        rcondf{1} 15. auto. progress. idtac=>/#.

        rcondt{1} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (Tweak.tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false)) <=> false by idtac=>/#. cut ->: Tweak.tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) =
   Tweak.tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite W.from_int_inj_fun => /#. done. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. by move : H4; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 30. auto; progress => /#. 
    rcondt{1} 40. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (Tweak.tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: Tweak.tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite W.from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite W.from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 45. auto; progress. cut ->: l{m0} = C.aa{m0}.[G.g{m0}] <=> false by idtac=> /#. cut ->: l{m0} = C.bb{m0}.[G.g{m0}] <=> false by idtac=>/#. by simplify.
     rcondt{1} 55. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 60. auto; progress. cut ->: l{m0} = C.aa{m0}.[G.g{m0}] <=> false by idtac=> /#. cut ->: l{m0} = C.bb{m0}.[G.g{m0}] <=> false by idtac=>/#. by simplify. 

     auto; progress. idtac=>/#. idtac=>/#. 

     rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 


        
inline*.

case (C.aa{2}.[G.g{2}] = l3{2}).
  rcondt{2} 3. auto.   

  rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 30. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
    rcondt{2} 40. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 45. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 
     rcondt{2} 55. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 60. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 

  rcondt{1} 3. auto. 

     rcondt{1} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 15. auto. progress. idtac=>/#.  
    rcondt{1} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 30. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
    rcondt{1} 40. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 45. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 
     rcondt{1} 55. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 60. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 


     auto; progress. idtac=>/#. idtac=>/#. 

     rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
        
rcondf{2} 3. auto. progress => /#.
rcondf{1} 3. auto. progress =>/#.

case (C.bb{2}.[G.g{2}] = l3{2}).
  rcondt{2} 3. auto; progress => /#. 

  rcondt{2} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#. 
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.  by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress => /#. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 46. auto; progress => /#. 
     rcondt{2} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress => /#. 

     rcondt{1} 3. auto; progress => /#. 

  rcondt{1} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 15. auto. progress. idtac=>/#. 
    rcondt{1} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.  by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 30. auto; progress => /#. 
    rcondt{1} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 46. auto; progress => /#. 
     rcondt{1} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 61. auto; progress => /#. 
     
     auto; progress. idtac=>/#. idtac=>/#. 

     rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

case (! C.bb{2}.[G.g{2}] <= l3{2}).
    rcondt{2} 3. auto; progress => /#. 
    rcondt{2} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#. 
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress => /#. 
    rcondt{2} 41. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 46. auto; progress => /#. 
    rcondt{2} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress => /#. 

     rcondt{1} 3. auto; progress => /#. 
    rcondt{1} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 15. auto. progress. idtac=>/#. 
    rcondt{1} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 30. auto; progress => /#. 
    rcondt{1} 41. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 46. auto; progress => /#. 
    rcondt{1} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 61. auto; progress => /#. 

auto; progress. idtac=>/#. idtac=>/#. 

     rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

    rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.     
     
rcondf{2} 3. auto; progress => /#. 
     rcondt{2} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#. 
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress => /#. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 46. auto; progress => /#. 
     rcondt{2} 57. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 62. auto; progress => /#. 

rcondf{1} 3. auto; progress => /#. 
     rcondt{1} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{1} 15. auto. progress. idtac=>/#. 
    rcondt{1} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 30. auto; progress => /#. 
    rcondt{1} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 46. auto; progress => /#. 
     rcondt{1} 57. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{m0}
     (tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
        (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ true)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ true) =
   tweak G.g{m0} (R.t{m0}.[C.aa{m0}.[G.g{m0}]] ^^ false)
     (R.t{m0}.[C.bb{m0}.[G.g{m0}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{m0}.[C.aa{m0}.[G.g{m0}]]); case (R.t{m0}.[C.bb{m0}.[G.g{m0}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{1} 62. auto; progress => /#. 


     auto; progress. idtac=>/#. idtac=>/#. 

     rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
        
     auto. progress. 
by idtac=>/#.  by rewrite in_fset0.
  by rewrite in_fset0.
  by rewrite in_fset0.
  by rewrite in_fset0. by rewrite in_fset0.  
     
while ((={l,b,glob A,b0,l0,lsb0,l1,query_ind,i0} /\ ={glob R, useVisible,lsb1,l2} /\ ={glob G,l3} /\ ES.SG.DKCSecurity.bound{1} = ES.SomeDKC.DKCSecurity.bound{2} /\ ES.SG.DKCSecurity.DKCp.b{1} = ES.SomeDKC.DKCSecurity.DKCp.b{2} /\ ES.SG.DKCSecurity.DKCp.l{1} = ES.SomeDKC.DKCSecurity.DKCp.l{2} /\ ES.SG.DKCSecurity.DKCp.lsb{1} = ES.SomeDKC.DKCSecurity.DKCp.lsb{2} /\ ES.SG.DKCSecurity.DKCp.ksec{1} = ES.SomeDKC.DKCSecurity.DKCp.ksec{2} /\ DKCSecurity.DKCp.used{1} = SomeDKC.DKCSecurity.DKCp.used{2} /\ ES.SG.DKCSecurity.DKCp.kpub{1} = ES.SomeDKC.DKCSecurity.DKCp.kpub{2} /\ l0{2} = l{1} /\ DKCSecurity.DKCp.l{1} = l0{1} /\ l1{1} = l{1} /\ l2{1} = l1{1} /\ useVisible{1} /\ l3{1} = l1{1} /\ l{2} = x /\ size R.t{2} = C.n{2} + C.q{2} /\ R.t{2}.[SomeDKC.DKCSecurity.DKCp.l{2}] = !SomeDKC.DKCSecurity.DKCp.lsb{2} /\ b0{2} = b{2} /\ b{2} /\ SomeDKC.DKCSecurity.DKCp.b{2} = b{2})
    /\
    ={glob A,real,p} /\ ={glob ES.SG.C} /\
      size ES.SG.C.v{1} = (ES.SG.C.n + ES.SG.C.q){1} /\
      ES.SG.C.f{1} = ((ES.SG.C.n, ES.SG.C.m, ES.SG.C.q, ES.SG.C.aa, ES.SG.C.bb), ES.SG.C.gg){1} /\
      ES.SG.validInputsP (ES.SG.C.f, ES.SG.C.x){1} /\
      (forall i, 0 <= i < ES.SG.C.n{2} => ES.SG.C.v{2}.[i] = ES.SG.C.x{2}.[i]) /\
      (forall i, ES.SG.C.n <= i < ES.SG.C.n + ES.SG.C.q => ES.SG.C.v{2}.[i] = oget ES.SG.C.gg.[(i, ES.SG.C.v{2}.[ES.SG.C.aa{2}.[i]], ES.SG.C.v{2}.[ES.SG.C.bb.[i]])]){2} /\

      (*(forall k, C.n{1} <= k < G.g{1} => mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ mem SomeDKC.DKCSecurity.DKCp.used{2} (Tweak.tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\*)
      
      0 <= i0{1} <= C.n{1} /\

      (forall k, 0 <= k < i0{1} => mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
      (forall k, i0{1} <= k < C.n{2} => !mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) ).

progress. inline*. rcondt{1} 5. auto. progress => /#. rcondf{1} 10. auto. progress. idtac=>/#. rcondt{2} 5. auto. progress => /#. rcondf{2} 10. auto. progress. idtac=>/#. (auto; progress; first 2 by idtac=>/#). rewrite ?in_fsetU ?in_fset1 => /#. rewrite ?in_fsetU ?in_fset1. cut ->: mem SomeDKC.DKCSecurity.DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ? : k <> i0{2} by idtac=>/#. by rewrite from_int_inj_fun => /#. 


    auto. progress.
    idtac=>/#. idtac=>/#. 

    by auto. done. done.
    
          cut ? : x < ES.SomeDKC.boundl by smt.
          byequiv (ES.SomeDKC.true_key x (ES.SG.DKC_Adv(A))). done. done.
  
          congr. cut ->: Pr[ES.SG.DKCSecurity.Game(ES.SG.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game
   (false, x) @ &m : !res] = Pr[ES.SomeDKC.DKCSecurity.Game(ES.SomeDKC.DKCSecurity.DKC_O, ES.SG.DKC_Adv(A)).game
   (false, x) @ &m : !res]. admit. cut ? : x < ES.SomeDKC.boundl by smt.
     byequiv (ES.SomeDKC.false_key x (ES.SG.DKC_Adv(A))). done. idtac=>/#. 
     done.

 

 
 case (ES.bound = 3) => hc. 
 rewrite (Mrplus.sum_rm _ _ 0). rewrite intval_def => /#.
 rewrite (Mrplus.sum_rm _ _ 1). rewrite ?in_fsetD intval_def in_fset1 => /#.
 rewrite (Mrplus.sum_rm _ _ 2). rewrite ?in_fsetD ?intval_def ?in_fset1 => /#.
 cut ->: (intval 0 (ES.bound - 1) `\` fset1 0 `\` fset1 1 `\` fset1 2) = fset0. rewrite fsetP => x. rewrite ?in_fsetD !in_fset1 intval_def in_fset0 => /#.
 rewrite hc. simplify. rewrite Mrplus.sum_empty. smt.
 



 
 
     elim/intind (ES.bound). simplify. simplify intval. rewrite List.Iota.iota0. done. rewrite -set0E. rewrite Mrplus.sum_empty. done. move => bound hbound hind.
     cut ->: (bound + 1)%r * eps_prf = bound%r * eps_prf + eps_prf by idtac=>/#.
     cut ->: bound + 1 - 1 = bound by idtac=>/#.

     

 
     rewrite (Mrplus.sum_rm _ _ (bound-1)). rewrite intval_def. smt. 
     cut ->: (intval 0 bound `\` fset1 (bound-1)) = (intval 0 (bound-1)).  rewrite fsetP. move => x. rewrite in_fsetD !intval_def in_fset1. idtac=>/#. simplify. cut ? : Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.PRFr_Wrapped, ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main
   (bound) @ &m : res] -
Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.RandomFunction, ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main
   (bound) @ &m : res] <= eps_prf. smt.
 
     rewrite intval_def.



 

print SomeOT.OTSecurity. 
print ProtSecurity.Protocol.input1_t.
print SomeOT.OTSecurity.OTPSec.Protocol.input1_t.

print ProtSecurity.Protocol.input2_t.
print SomeOT.OTSecurity.OTPSec.Protocol.input2_t.
print SomeOT.OTSecurity.OT.msg_t.

print ES.

print SomeOT.

lemma Security eps_ESn eps_DDH eps_prf i : 
  forall (A1 <: ProtSecurity.Adv1_t {ES.Rand, CSFE.B_OT1, CSFE.B_G, SomeOT.DDHn_A, SomeOT.ESn_A}) (A2 <: ProtSecurity.Adv2_t {ES.Rand, CSFE.B_OT2, CSFE.B_G}) (A <: ES.SG.Sec.EncSecurity.Adv_IND_t{ES.SG.Rand,ES.SG.R,ES.SG.C,ES.SG.DKC_Adv,ES.SomeDKC.DKCSecurity.DKCp,ES.SomeDKC.DKCSecurity.DKC_O}) &m,
   islossless A1.gen_query =>
   islossless A1.dist =>
   islossless A2.gen_query =>
   islossless A2.dist =>
   `|2%r * Pr[SomeOT.ESn.Game(SomeOT.ESn_A(CSFE.B_OT1(ES.Rand ,SFE_A1(A1)))).main()@ &m:res] - 1%r| <= eps_ESn =>
   `|2%r * Pr[DDH.DDH.Game(SomeOT.DDHn.DDHnmax.ADDH(SomeOT.DDHn.ADDHnmax(SomeOT.DDHn_A(CSFE.B_OT1(ES.Rand, SFE_A1(A1)))))).main()@ &m:res] - 1%r| <= eps_DDH =>
    0 <= i < ES.SG.bound => 
    (Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.PRFr_Wrapped,ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main(i)@ &m:res] - Pr[ES.SomeDKC.PRF.IND(ES.SomeDKC.PRF.RandomFunction,ES.SomeDKC.D(ES.SG.DKC_Adv(A))).main(i)@ &m:res]) <= eps_prf =>
    
   let epsilon = eps_ESn + SomeOT.max_size%r * eps_DDH + ES.SG.bound%r * eps_prf in
   `|2%r * Pr[ProtSecurity.Game1(R1, R2, S, A1).main() @ &m : res] - 1%r| <= epsilon /\
   `|2%r * Pr[ProtSecurity.Game2(R1, R2, S, A2).main() @ &m : res] - 1%r| <= epsilon.
proof.
  progress.




      admit. qed.

(*      (* François: - We can replace epsilon by 0%r in the last line is it normal ? *)
 proof strict.
 intros A1 A2 &m A1genll A1distll A2genll A2distll bound.

 cut Randgenll : islossless ES.Rand.gen by apply ES.Rand_islossless.
 cut Ssim1ll : islossless SomeOT.S.sim1 by apply SomeOT.S1_lossless.
 cut SFE_A1genll  : islossless SFE_A1(A1).gen_query by (fun; call A1genll; trivial).
 cut SFE_A1distll : islossless SFE_A1(A1).dist      by (fun; call A1distll;trivial).
 cut SFE_A2genll  : islossless SFE_A2(A2).gen_query by (fun; call A2genll; trivial).
 cut SFE_A2distll : islossless SFE_A2(A2).dist      by (fun; call A2distll;trivial).
 cut B_OT1_gen_ll : islossless CSFE.B_OT1(ES.Rand ,SFE_A1(A1)).gen_query
  by (apply (CSFE.B_OT1_gen_ll ES.Rand (SFE_A1(A1)) _ _)=> //).
 cut B_OT1_dist_ll : islossless CSFE.B_OT1(ES.Rand ,SFE_A1(A1)).dist
  by (apply (CSFE.B_OT1_dist_ll ES.Rand (SFE_A1(A1)) _)=> //).
 cut B_OT2_gen_ll : islossless CSFE.B_OT2(ES.Rand ,SFE_A2(A2)).gen_query
  by (apply (CSFE.B_OT2_gen_ll ES.Rand (SFE_A2(A2)) _ _)=> //).
 cut B_OT2_dist_ll : islossless CSFE.B_OT2(ES.Rand ,SFE_A2(A2)).dist
  by (apply (CSFE.B_OT2_dist_ll ES.Rand (SFE_A2(A2)) _)=> //).
 cut B_G_gen_ll : islossless CSFE.B_G(SomeOT.S, SFE_A1(A1)).gen_query
  by (apply (CSFE.B_G_gen_ll SomeOT.S (SFE_A1(A1)) _)=> //).
 cut B_G_dist_ll : islossless CSFE.B_G(SomeOT.S, SFE_A1(A1)).get_challenge
  by (apply (CSFE.B_G_dist_ll SomeOT.S (SFE_A1(A1)) _)=> //).

 elim (Connect_SFE (SFE_A1(A1)) (SFE_A2(A2)) &m _ _ _ _)=> //.
 elim (SomeOT.ot_is_sec (CSFE.B_OT1(ES.Rand ,SFE_A1(A1))) (CSFE.B_OT2(ES.Rand ,SFE_A2(A2))) &m _ _ _ _
  `|2%r * Pr[SomeOT.ESn.Game(SomeOT.ESn_A(CSFE.B_OT1(ES.Rand ,SFE_A1(A1)))).main() @ &m : res] - 1%r|
  `|2%r * Pr[DDH.DDHn.Game(SomeOT.DDHn_A(CSFE.B_OT1(ES.Rand, SFE_A1(A1)))).main() @ &m : res] - 1%r| _ _)=> //.
 cut := ES.sch_is_sim  (CSFE.B_G(SomeOT.S, SFE_A1(A1))) &m _ _=> //.

 rewrite (Connect_DKCScheme_pr (CSFE.B_G(SomeOT.S, SFE_A1(A1))) &m) //.
 rewrite (Connect_SFE_2_pr (A2) &m) // (Connect_SFE_1_pr (A1) &m) //.
 rewrite (Connect_SomeOT_1_pr (CSFE.B_OT1(ES.Rand ,SFE_A1(A1))) &m) //.
 rewrite (Connect_SomeOT_2_pr (CSFE.B_OT2(ES.Rand ,SFE_A2(A2))) &m) //.

 rewrite /bound.

 clear A1genll A1distll A2genll A2distll bound Randgenll Ssim1ll SFE_A1genll SFE_A1distll SFE_A2genll
   SFE_A2distll B_OT1_gen_ll B_OT1_dist_ll B_OT2_gen_ll B_OT2_dist_ll B_G_gen_ll B_G_dist_ll.

 progress;smt.
 qed.*)
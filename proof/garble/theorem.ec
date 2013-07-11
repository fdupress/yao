require import Real.

(* Import some common defs *)
require import PreProof.

(* We assume that DKC is correct *)
axiom DkcCorrect :
  forall (t k1 k2 m:Dkc.t),
    GC.DKC.decode t k1 k2 (GC.DKC.encode t k1 k2 m) = m.

(* Get the main lemma for correction proof *)
require CorrectionProof.

(* Proof that GarbleCircuit is Correct *)
require Garble.
clone Garble.Correct as GCorrect with
  theory Garble = GC.GarbleCircuit
  proof Correct.
realize Correct.
intros f x i h1 h2.
apply (CorrectionProof.correct _ f x i _ _)=> //.
apply DkcCorrect.
qed.

(* We assume that DKC is secure *)
axiom DkcSecure :
  exists (epsilon:real), epsilon > 0%r /\
    forall (A<:DKCS.Adv_t), forall &m,
      `|2%r * Pr[DKCS.Game(DKCS.Dkc, A).main()@ &m:res] - 1%r| < epsilon.

(* Get the reduction proof *)
require ReductionProof.

(* Proof that GarbleCircuit is INDCPA for PrvInd *)
clone Garble.PrvInd as PrvInd_Circuit with
  theory Garble = GC.GarbleCircuit.
require INDCPA.
clone INDCPA.Sec as PrvIndSec with
  theory INDCPA_Scheme = PrvInd_Circuit.INDCPA_Scheme
  proof Sec by admit.
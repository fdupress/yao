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

(* Section should remove this *)
require Reduction.
require ReductionAda.
require EquivFake.

(* Get the reduction proof *)
require ReductionProof.

(* Proof that garble reduce to DKC *)
lemma PrvIndDkc :
  exists (Rand<:PrvIndSec.Rand_t),
    forall (ADVG<:PrvIndSec.Adv_t{PrvIndSec.Game}),
      islossless ADVG.gen_query =>
      islossless ADVG.get_challenge =>
      exists (ADVD<:DKCS.Adv_t),
        forall &m,
          `|Pr[PrvIndSec.Game(Rand, ADVG).main()@ &m:res] - 1%r / 2%r| =
             2%r * Cst.bound%r * `|Pr[DKCS.Game(DKCS.Dkc, ADVD).main()@ &m:res] - 1%r / 2%r| by apply ReductionProof.PrvIndDkc.

(* Assume that DKC is secure *)
axiom DkcSecure :
  exists (epsilon:real), epsilon > 0%r /\
    forall (A<:DKCS.Adv_t), forall &m,
      `|Pr[DKCS.Game(DKCS.Dkc, A).main()@ &m:res] - 1%r / 2%r| < epsilon.

(* We get garble secure *)
lemma GarbleSec :
  exists (RAND <: PrvIndSec.Rand_t) (epsilon:real), epsilon > 0%r /\
    forall (ADV<:PrvIndSec.Adv_t{PrvIndSec.Game}), forall &m,
      islossless ADV.gen_query =>
      islossless ADV.get_challenge =>
        `|Pr[PrvIndSec.Game(RAND, ADV).main()@ &m:res] - 1%r / 2%r| < epsilon.
proof strict.
  elim DkcSecure=> epDkc [hPos hDkc].
  elim PrvIndDkc=> RAND redu.
  exists RAND.
  exists (2%r*(Cst.bound%r)*epDkc).
  split;first smt.
  intros ADVG &m ? ?.
  elim (redu ADVG _ _)=> {redu} // ADVD redu.
  rewrite (redu &m).
  apply (_:forall a c d, a > 0%r  => c < d => a*c < a*d);first admit.
  smt.  
  apply (hDkc ADVD &m).
save.
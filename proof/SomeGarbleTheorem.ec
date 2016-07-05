require import Real.
require import Int.
require import IntDiv.
require import FSet.
require import NewFMap.
require import Array.
require import Distr.
require import Bool.
require import Pair.
require import DInterval.
require import Option.

require import GarbleTools.
  
require import ArrayExt.

import ForLoop.

require import SomeGarble.

import GSch.Sch.
import W.
import SomeGarble.DKCSecurity.
import SomeGarble.Tweak.

require import SomeGarbleReal.
require import SomeGarbleFake.
require import SomeGarbleHy.
require import SomeGarbleReduce.

lemma reductionSimplified (A <: GSch.EncSecurity.Adv_IND_t{Rand,R,C,DKC_Adv,DKCp}) &m:
  Pr[GameHybrid(A).garble(-1) @ &m : res] - Pr[GameHybrid(A).garble(SomeGarble.bound-1) @ &m : res] =
  (SomeGarble.bound)%r * (2%r * Pr[DKCSecurity.Game(DKC, DKC_Adv(DKCSecurity.DKC, A)).main()@ &m:res] - 1%r).
proof. admit. qed.

lemma sch_is_ind (A <: GSch.EncSecurity.Adv_IND_t{Rand,R,R',G,C,DKCp}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>    
  `|2%r * Pr[GSch.EncSecurity.Game_IND(Rand,A).main()@ &m:res] - 1%r| =
    2%r * (SomeGarble.bound)%r * `|2%r * Pr[DKCSecurity.Game(DKC, SomeGarbleReduce.DKC_Adv(DKCSecurity.DKC, A)).main()@ &m:res] - 1%r|.
proof.
  move => AgenL AgetL.
  rewrite -(GameHybrid0_Game_IND_pr A &m) // -{1}(GameHybridBound_pr A &m) //=.
  cut -> : forall a b, 2%r * a - 2%r * b = 2%r * (a - b) by idtac=>/#. 
  rewrite (reductionSimplified A &m).
  cut H: forall (a b:real), 0%r <= a => `| a * b | = a * `| b | by idtac=>/#.
  rewrite !H=> //; first by smt. 
  by idtac=>/#.
qed.

(*lemma sch_is_sim (A <: GSch.EncSecurity.Adv_SIM_t {Rand, DKCp}) &m:
 islossless A.gen_query =>
 islossless A.get_challenge =>
  `|2%r * Pr[GSch.EncSecurity.Game_SIM(Rand,GSch.EncSecurity.SIM(Rand),A).main()@ &m:res] - 1%r| <=
    2%r * (SomeGarble.bound)%r * `|2%r * Pr[DKCSecurity.Game(DKC,GSch.EncSecurity.RedI(A)).main()@ &m:res] - 1%r|.
proof.
  move=> ll_ADVp1 ll_ADVp2.
  rewrite -(sch_is_ind (EncSecurity.RedSI(A)) _ _ &m).
    by apply (EncSecurity.RedSIgenL A).
    by apply (EncSecurity.RedSIgetL A).
  apply (EncSecurity.ind_implies_sim Rand A _ _ &m _)=> //.
  by apply sch_is_pi.
qed.*)

(*lemma gsch_is_sim (A <: GSch.EncSecurity.Adv_SIM_t {R}) (Adv <: Adv_DKC_t) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
    `|2%r * Pr[GSch.EncSecurity.Game_SIM(Rand,GSch.EncSecurity.SIM(Rand),A).main()@ &m:res] - 1%r| <=
    2%r * (SomeGarble.bound)%r * `|2%r * Pr[DKCSecurity.Game(DKC, SomeGarbleReduce.DKC_Adv(DKCSecurity.DKC, RedSI(A))).main()@ &m:res] - 1%r|.*)
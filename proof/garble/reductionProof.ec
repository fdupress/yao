require import Bool.
require import Real.
require import Int.
require import Fun.
require import FSet.
require import Monoid.

require import GarbleTools.
require import PreProof.
require import ClonesMean.
require import Reduction.
require import ReductionAda.
require import EquivReal.
require import EquivHybrid.
require import EquivFake.
require import EquivAda.

lemma inv : forall (a:real), a <> 0%r=>  (a / a) = 1%r by smt.
lemma unit : forall (a:real), a * 1%r = a by smt.
lemma simpl : forall (a b:real), b <> 0%r=>  (a / b * b) = a by smt.
lemma invadd : forall (a b : real), a - b = Real.(+) a (-b) by smt.
lemma midiv : forall (a b : real), - a / b = (-a) / b by smt.

lemma prReal :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, PrvIndSec.Game}),
    forall &m,
    Pr[RedEspTrue.RedWork(ADV).work(0) @ &m : res] =
      Pr[PrvIndSec.Game(ADV).main() @ &m : res].
proof strict.
intros=> ADV &m.
cut := RedEspTrue.RemRedEsp (lambda x, x) ADV &m &m 0=> /= ->.
equiv_deno (realEq ADV)=> //.
save.

lemma prHybrid :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, PrvIndSec.Game}),
    forall &m x,
      0 <= x <= Cst.bound - 1 =>
    let y = x + 1 in
    Pr[RedEspFalse.RedWork(ADV).work(x) @ &m : !res] =
      Pr[RedEspTrue.RedWork(ADV).work(y) @ &m : res].
proof strict.
intros=> ADV &m ? ? ?.
cut := RedEspFalse.RemRedEsp (lambda x, !x) ADV &m &m x=> /= ->.
cut := RedEspTrue.RemRedEsp (lambda x, x) ADV &m &m y=> /= ->.
equiv_deno (hybridEq ADV x _)=> //.
by intros ? ?;case res{1};case res{2}=> //.
save.

lemma prFake :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, Fake}),
    forall &m,
      islossless ADV.gen_query =>
      islossless ADV.get_challenge =>
        let x = Cst.bound - 1 in
        Pr[RedEspFalse.RedWork(ADV).work(x)@ &m : !res] = 1%r / 2%r.
proof strict.
intros=> ADV &m ? ? /=.
cut := RedEspFalse.RemRedEsp (lambda x, !x) ADV &m &m (Cst.bound - 1)=> /= ->.
rewrite -(fakePr ADV &m) //.
equiv_deno (fakeEq ADV)=> //.
save.

lemma prAda :
  forall (ADV <: PrvIndSec.Adv_t{Red, DKCS.Dkc}),
    forall &m,
      Pr[DKCS.Game(DKCS.Dkc, Red(ADV)).main()@ &m : res] =
        Pr[DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).main()@ &m : res].
proof strict.
intros=> ADV &m.
equiv_deno (adaEq ADV)=> //.
save.

lemma RelDkcGarble :
  forall (ADV<:PrvIndSec.Adv_t{DKCS.Dkc,DKCS.Game,RedAda,Fake,MeanBool.Rand,MeanInt.Rand}),
    islossless ADV.gen_query =>
    islossless ADV.get_challenge =>
      forall &m,
        Pr[PrvIndSec.Game(ADV).main()@ &m:res] =
          2%r * Cst.bound%r * Pr[DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).main()@ &m:res]
            + 1%r / 2%r - Cst.bound%r.
proof strict.
  intros ADV ? ? &m .
  rewrite (DkcEsp &m (RedAda(ADV))).
  cut := RedEspTrue.AdvEsp &m ADV;delta RedEspTrue.b=> /= ->.
  cut := RedEspFalse.AdvEsp &m ADV;delta RedEspFalse.b=> /= ->.

  cut -> : ((lambda (l : int), Pr[RedEspFalse.RedWork(ADV).work(l) @ &m : res] / (Cst.bound)%Cst%r) =
   (lambda (l : int), (1%r - Pr[RedEspFalse.RedWork(ADV).work(l) @ &m : !res]) / (Cst.bound)%Cst%r));
    first by apply fun_ext=> x /=;rewrite Pr mu_not;
             rewrite (RedEspFalse.RedEspT x &m ADV) //;smt.

  rewrite /suppInt.

  rewrite (Mrplus.sum_rm _ _ 0) /=;first by rewrite Interval.mem_interval;smt.
  rewrite (Mrplus.sum_chind _ (lambda (x:int), x - 1) (lambda (x:int), x + 1)) /=;
    first smt.
  rewrite (Interval.dec_interval 0 (Cst.bound-1) _);first smt.
  rewrite (Mrplus.sum_rm _ (Interval.interval 0 (Cst.bound - 1)) ((Cst.bound)%Cst - 1)) /=;
    first rewrite Interval.mem_interval;first smt.

  pose s1 := Mrplus.sum _ _.
  pose s2 := Mrplus.sum _ _.
  rewrite -(Mrplus.Base.addmC s2) Mrplus.Base.addmA -(Mrplus.Base.addmA _ s1).
  delta s1 s2.
  clear s1 s2.
  rewrite Mrplus.sum_add2 /=.

  rewrite -(prReal ADV &m).
  cut := prFake ADV &m=> /= -> //.

  rewrite (Mrplus.NatMul.sum_const (1%r/Cst.bound%r));
    first by intros=> x;
    rewrite mem_rm Interval.mem_interval=> [h1 h2];
    cut := prHybrid ADV &m x=> /= -> //;smt.
  delta Mrplus.NatMul.( * ) Mrplus.Base.( + )=> /=.

rewrite card_rm_in.
rewrite Interval.mem_interval;
  first by split;[smt| intros=> _;apply Refl].
rewrite Interval.card_interval_max.
rewrite (_:(max ((Cst.bound)%Cst - 1 - 0 + 1) 0) = Cst.bound);first smt.
pose a := Pr[RedEspTrue.RedWork(ADV).work(0) @ &m : res].
rewrite Sub.
pose b := (Cst.bound)%r.
delta Brplus.(+).
rewrite sub_div;first smt.
rewrite Real.Comm.Comm.
rewrite assoc_mul_div;first smt.
rewrite -(Real.Comm.Comm b).
rewrite assoc_mul_div;first smt.
rewrite !inv;first 2 smt.
rewrite !Real.Mul_distr_r.
rewrite ! unit.
rewrite ! simpl;first 2 smt.
rewrite (invadd 1%r).
rewrite !Real.Mul_distr_r.
rewrite midiv.
rewrite simpl;first smt.
smt.
save.

lemma _PrvIndDkc :
  forall (ADVG<:PrvIndSec.Adv_t{DKCS.Dkc,DKCS.Game,RedAda,Red,Fake,MeanBool.Rand,MeanInt.Rand}),
    islossless ADVG.gen_query =>
    islossless ADVG.get_challenge =>
    exists (ADVD<:DKCS.Adv_t),
      forall &m,
        `|Pr[PrvIndSec.Game(ADVG).main()@ &m:res] - 1%r / 2%r| =
           2%r * Cst.bound%r * `|Pr[DKCS.Game(DKCS.Dkc, ADVD).main()@ &m:res] - 1%r / 2%r|.
proof strict.
  intros ADVG ? ?.
  exists (Red(ADVG)).
  intros &m.
  rewrite (RelDkcGarble ADVG _ _ &m) //.
  rewrite (prAda ADVG &m).
  pose p := Pr[DKCS.GameAda(DKCS.Dkc, RedAda(ADVG)).main() @ &m : res].
  cut -> : forall y z c, 2%r * y * z + c - y - c = 2%r * y * (z - (1%r / 2%r)) by smt.
  cut -> : forall (a b:real), a >= 0%r => `| a * b | = a * `| b | by smt;
  [smt|by trivial].
save.


lemma PrvIndDkc :
  forall (ADVG<:PrvIndSec.Adv_t{PrvIndSec.Game}),
    islossless ADVG.gen_query =>
    islossless ADVG.get_challenge =>
    exists (ADVD<:DKCS.Adv_t),
      forall &m,
        `|Pr[PrvIndSec.Game(ADVG).main()@ &m:res] - 1%r / 2%r| =
           2%r * Cst.bound%r * `|Pr[DKCS.Game(DKCS.Dkc, ADVD).main()@ &m:res] - 1%r / 2%r|.
proof strict.
  admit. (* Need section *)
save.
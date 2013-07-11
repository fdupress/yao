require import Real.
require import Bool.

(*
lemma math :
forall (x:real) (b:int),
x =
2%r * b%r *
((1%r / b%r * x + 1%r / b%r * (1%r / 2%r) + (b%r - 1%r) * (1%r / b%r)) / 2%r) +
1%r / 2%r - b%r.
(*smt "Mathematica".*)
admit.
save.
lemma simpl : (forall (x y z:real), y>0%r=> x < z  => x * y < y * z) by [].
*)

require import Int.
require import Fun.
require import Set.

require import GarbleTools.
require import PreProof.
require import ClonesMean.
require import Reduction.
require import ReductionAda.
require import EquivReal.
require import EquivHybrid.
require import EquivFake.
(*require import EquivAda.*)

(*
require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Bool.
require import Distr.
require import Fun.
require import Logic.

require import MyTools.
require import Garble.
require import GarbleTools.
require import Myset.
require import MyMean.
*)

lemma prReal :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, PrvIndSec.Game}),
    forall &m,
    Pr[RedEspTrue.RedWork(ADV).work(0) @ &m : res] =
      Pr[PrvIndSec.Game(RandGarble2, ADV).main() @ &m : res].
proof.
intros=> ADV &m.
cut := RedEspTrue.RemRedEsp (lambda x, x) ADV &m &m 0=> /= ->.
equiv_deno (realEq ADV)=> //.
save.

lemma prHybrid :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, PrvIndSec.Game}),
    forall &m x,
      x >= 0 /\ x < Cst.bound =>
    let y = x + 1 in
    Pr[RedEspFalse.RedWork(ADV).work(x) @ &m : res] =
      Pr[RedEspTrue.RedWork(ADV).work(y) @ &m : !res].
proof.
intros=> ADV &m ? ? ?.
cut := RedEspFalse.RemRedEsp (lambda x, x) ADV &m &m x=> /= ->.
cut := RedEspTrue.RemRedEsp (lambda x, !x) ADV &m &m y=> /= ->.
equiv_deno (hybridEq ADV x)=> //.
save.

lemma prFake :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, Fake}),
    forall &m,
      islossless ADV.gen_query =>
      islossless ADV.get_challenge =>
        let x = Cst.bound - 1 in
        Pr[RedEspFalse.RedWork(ADV).work(x)@ &m : !res] = 1%r / 2%r.
proof.
intros=> ADV &m ? ? /=.
cut := RedEspFalse.RemRedEsp (lambda x, !x) ADV &m &m (Cst.bound - 1)=> /= ->.
rewrite -(fakePr ADV &m) //.
equiv_deno (fakeEq ADV)=> //.
save.

lemma RelDkcGarble :
  forall &m,
    forall (ADV<:PrvIndSec.Adv_t{DKCS.Dkc,DKCS.Game,RedAda}),
      Pr[PrvIndSec.Game(RandGarble2, ADV).main()@ &m:res] =
        2%r * Cst.bound%r * Pr[DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).main()@ &m:res]
          + 1%r / 2%r - Cst.bound%r.
proof.
  intros &m ADV.
  rewrite (DkcEsp &m (RedAda(ADV))).
  rewrite (RedEspTrue.AdvEsp &m ADV true) //=.
  rewrite (RedEspFalse.AdvEsp &m ADV false) //=.

(**Remove Pr*)
  pose f := (lambda l, Pr[RedEspTrue.RedWork(ADV).work(l) @ &m : res]).
  rewrite (_:(lambda (l : int),
    Pr[RedEspTrue.RedWork(ADV).work(l) @ &m : res] / Cst.bound%r) =
      lambda (l : int), 1%r / Cst.bound%r * (f l));
    first (apply fun_ext=> l //).
(**End Remove Pr*)

(**Remove Pr*)
  pose g := (lambda l, Pr[RedEspFalse.RedWork(ADV).work(l) @ &m : res]).
  rewrite (_:(lambda (l : int),
    Pr[RedEspFalse.RedWork(ADV).work(l) @ &m : res] / Cst.bound%r) =
      lambda (l : int), 1%r / Cst.bound%r * (g l));
    first (apply fun_ext=> l //).
(**End Remove Pr*)

(**Remove Pr*)
  cut -> : (Pr[PrvIndSec.Game(RandGarble2, ADV).main() @ &m : res] = f 0).
  rewrite /f. (prReal ADV &m) //.
cut valf0 : (f 0 = Pr[Game(PrvInd(RandGarble), Adv).main() @ &m : res{hr}]).
  rewrite (fv 0).
rewrite <- valf0.
(**End Remove Pr*)

  rewrite (sum_rm<:int>
   (lambda (l : int), 1%r / borne%r * (f l))
   MeanInt.support
   0 _);first smt.
  rewrite (sum_rm<:int>
   (lambda (l : int), 1%r / borne%r * (g l))
   MeanInt.support
   (borne-1) _);first smt.
simplify.
rewrite ( _ :
1%r / borne%r * f 0 +
  sum (lambda (l : int), 1%r / borne%r * f l)
    (rm 0 MeanInt.support) +
  (1%r / borne%r * g (borne-1) +
   sum (lambda (l : int), 1%r / borne%r * g l)
     (rm (borne-1) MeanInt.support))
=
1%r / borne%r * (f 0) +
1%r / borne%r * (g (borne-1)) +
(
sum (lambda (l : int), 1%r / borne%r * (f l)) (rm 0 MeanInt.support) +
sum (lambda (l : int), 1%r / borne%r * (g l)) (rm (borne-1) MeanInt.support)
)
);first smt.

  rewrite (sum_chind<:int>
    (lambda (l : int),
       1%r / borne%r * (f l))
    (lambda (x:int), x - 1)
    (lambda (x:int), x + 1)
    (rm 0 MeanInt.support) _);first smt.
  simplify.
  delta MeanInt.support.
  rewrite (dec_integers 0 borne _);first smt.
  rewrite (sum_add2<:int>
    (lambda (l : int), 1%r / borne%r * f (l+1))
    (lambda (l : int), 1%r / borne%r * g l)
    (rm (borne-1) (integers 0 borne))).
  simplify.
  cut lem : (forall x, mem x (rm (borne-1) (integers 0 borne)) =>
    f (Int.(+) x 1) = 1%r - g x).
      intros x h.
      rewrite (fv (x+1)).
      rewrite (gv x).
      rewrite (prHybrid (<:Adv) &m x _);first smt.
      apply (MeanInt.Not &m (<:AdvEspTrue.AdvWork(Adv)) (x + 1)).
    
  rewrite (sum_in<:int> (lambda (x : int),
       1%r / borne%r * f (Int.(+) x 1) +
       1%r / borne%r * g x) (rm (borne-1) (integers 0 borne))).
  simplify.
  rewrite (_ : (lambda (x:int),
(if mem x (rm (borne-1) (integers 0 borne)) then
         1%r / borne%r * f (Int.(+) x 1) +
         1%r / borne%r * g x
       else 0%r))
= (lambda (x:int), if mem x (rm (borne-1) (integers 0 borne)) then 1%r / borne%r else 0%r)
);first (apply Fun.extensionality;smt).
  rewrite (sum_const<:int> (1%r/borne%r)
(lambda (x : int),
       if mem x (rm (Int.(-) borne 1) (integers 0 borne)) then 1%r / borne%r
       else 0%r)
(rm (Int.(-) borne 1) (integers 0 borne))
_
);first smt.
cut valgborne : (g (borne-1) = 1%r / 2%r).
  rewrite (gv (borne-1)).
  apply (prFake (<:Adv) &m).
rewrite valgborne.
rewrite (_:(card (rm (Int.(-) borne 1) (integers 0 borne)))%r = borne%r - 1%r).
smt.
apply math.
save.

lemma PrvIndGarble :
  exists (epsilon:real), epsilon > 0%r /\
    forall (Adv<:Garble.Adv{DKC.Dkc,DKC.Game,Red}), forall &m,
        `|Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] - 1%r / 2%r| < epsilon.
proof.
  elim DkcSecure=> epDkc [hPos hDkc].
  exists (bound%r*epDkc).
  cut bPos : (bound%r > 0%r);first smt.
  progress;first smt.
  rewrite RelDkcGarble.
  cut remPr : (forall (x:real), `|2%r * x - 1%r| < epDkc => `|2%r * borne%r * x +
  1%r / 2%r - borne%r - 1%r / 2%r| < borne%r * epDkc).
    intros x h.
    rewrite (_:`|2%r * borne%r * x + 1%r / 2%r - borne%r - 1%r / 2%r| = `|2%r * x - 1%r| * `| borne%r|);first smt.
  rewrite (_:(`|borne%r| = borne%r));first smt.
  apply (simpl (`|2%r * x - 1%r|) (borne%r) epDkc);assumption.
  apply (remPr Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv)).main() @ &m :res{hr}] _).
  apply (hDkc (<:AdvGarble.Adv(Adv)) &m).
save.
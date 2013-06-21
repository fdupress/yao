require import Real.

lemma math :
forall (x:real) (b:int),
x =
2%r * b%r *
((1%r / b%r * x + 1%r / b%r * (1%r / 2%r) + (b%r - 1%r) * (1%r / b%r)) / 2%r) +
1%r / 2%r - b%r.
smt "Mathematica".
save.

require import Int.

lemma simpl : (forall (x y z:real), y>0%r=> x < z  => x * y < y * z) by [].

require import Fun.
require import Set.

require import MySum.
require import MyInt.

require AdvGarble.
require import Garble.
require import ClonesMean.
require import CloneDkc.

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
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &m,
    Pr[AdvEspTrue.AdvWork(ADV).work(0) @ &m : res] =
      Pr[Garble.Game(Garble.PrvInd(RandGarble), ADV).main() @ &m : res].
proof.
  rewrite (AdvEspTrue.RemAdvEsp

save.

lemma prHybrid :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &m x,
      x >= 0 /\ x < borne =>
    let y = x + 1 in
    Pr[AdvEspFalse.AdvWork(ADV).work(x) @ &m : res] =
      Pr[AdvEspTrue.AdvWork(ADV).work(y) @ &m : !res].
proof.
  admit.
save.

lemma prFake :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1,
        let x = borne - 1 in
        Pr[AdvEspFalse.AdvWork(ADV).work(x)@ &1 : res] = 1%r / 2%r.
proof.
  admit.
save.

lemma RelDkcGarble :
  forall &m,
    forall (Adv<:Garble.Adv{DKC.Dkc,DKC.Game,AdvGarble.Adv}),
      Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] =
        2%r * borne%r * Pr[GameAda(DKC.Dkc, ADV).work()@ &m:res]
          + 1%r / 2%r - borne%r.
proof.
  intros &m Adv.
  rewrite (DkcEsp &m (<:AdvGarble.Adv(Adv))).
  rewrite (AdvEspTrue.AdvEsp &m (<:Adv) true).
  rewrite (AdvEspFalse.AdvEsp &m (<:Adv) false).

(**Remove Pr*)
  cut introF : (exists (f:int->real), (forall (l:int), (f l) =
    Pr[AdvEspTrue.AdvWork(Adv).work(l) @ &m : res{hr}]));first
    (exists (lambda (l:int), Pr[AdvEspTrue.AdvWork(Adv).work(l) @ &m : res{hr}]);
     simplify;split).
  elim introF.
  intros f fv.
  rewrite (_:(lambda (l : int),
       1%r / borne%r *
       Pr[AdvEspTrue.AdvWork(Adv).work(l) @ &m : res{hr}]) = lambda (l : int),
       1%r / borne%r * (f l));
    first (apply Fun.extensionality;delta Fun.(==);simplify;intros l;rewrite (fv l);split).
(**End Remove Pr*)

(**Remove Pr*)
  cut introG : (exists (g:int->real), (forall (l:int), (g l) =
    Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}]));first
    (exists (lambda (l:int), Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}]);
     simplify;split).
  elim introG.
  intros g gv.
  rewrite (_:(lambda (l : int),
       1%r / borne%r *
       Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}]) = lambda (l : int),
       1%r / borne%r * (g l));
    first (apply Fun.extensionality;delta Fun.(==);simplify;intros l;rewrite (gv l);split).
(**End Remove Pr*)

(**Remove Pr*)
cut valf0 : (f 0 = Pr[Game(PrvInd(RandGarble), Adv).main() @ &m : res{hr}]).
  rewrite (fv 0).
  apply (prReal (<:Adv) &m).
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
    forall (Adv<:Garble.Adv{DKC.Dkc,DKC.Game,AdvGarble.Adv}), forall &m,
        `|Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] - 1%r / 2%r| < epsilon.
proof.
  elim DKC.Security.
  intros epDkc hDkc.
  elim hDkc. clear hDkc.
  intros hPos hDkc.

  exists (borne%r*epDkc).

  cut bPos : (borne%r > 0%r);first smt.
  progress;first smt.
  rewrite (RelDkcGarble &m (<:Adv)).
  cut remPr : (forall (x:real), `|2%r * x - 1%r| < epDkc => `|2%r * borne%r * x +
  1%r / 2%r - borne%r - 1%r / 2%r| < borne%r * epDkc).
    intros x h.
    rewrite (_:`|2%r * borne%r * x + 1%r / 2%r - borne%r - 1%r / 2%r| = `|2%r * x - 1%r| * `| borne%r|);first smt.
  rewrite (_:(`|borne%r| = borne%r));first smt.
  apply (simpl (`|2%r * x - 1%r|) (borne%r) epDkc);assumption.
  apply (remPr Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv)).main() @ &m :res{hr}] _).
  apply (hDkc (<:AdvGarble.Adv(Adv)) &m).
save.
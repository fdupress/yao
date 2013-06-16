require import Int.
require import Real.

lemma simpl : (forall (x y z:real), y>0%r=> x < z  => x * y < y * z) by [].

require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Bool.
require import Distr.
require import Fun.
require import Logic.

require import MyDkc.
require import MyTools.
require import Garble.
require import GarbleTools.
require AdvGarble.
require import Mean.
require import Myset.

lemma prReal :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1 &2,
      (glob ADV){1} = (glob ADV){2} /\
      (DKC.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=0) =>
    Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(ADV)).work() @ &1 : res] =
      Pr[Garble.Game(Garble.PrvInd(RandGarble), ADV).main() @ &2 : res].
proof.
  admit.
save.

lemma prHybrid :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1 &2,
      (glob ADV){1} = (glob ADV){2} =>
      (DKC.Dkc.b{1}) /\ (!DKC.Dkc.b{2}) =>
      (AdvGarble.Adv.l{2}=AdvGarble.Adv.l{1}+1) =>
    Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(ADV)).work() @ &1 : res] =
      Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(ADV)).work() @ &2 : res].
proof.
  admit.
save.

lemma fakePr :
  forall (ADV <: Garble.Adv{AdvGarble.Adv}),
    forall &1,
      (DKC.Dkc.b{1}) /\ (AdvGarble.Adv.l{1}=borne) =>
        Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(ADV)).work()@ &1 : res] = 1%r / 2%r.
proof.
  admit.
save.

clone Mean as MeanBool with
  type base = bool,
  op d = Dbool.dbool,
  op support = Set.add false (Set.add true Set.empty).

op integers : int -> int -> int set.

axiom integers_neg : forall (x y:int), x > y => integers x y = Set.empty.
axiom integers_pos : forall (x y:int), x <= y => integers x y = add y (integers x (y-1)).

clone Mean as MeanInt with
  type base = int,
  op d = Dinter.dinter 0 (borne),
  op support = integers 0 borne.

module DkcWorkAdv(Adv:DKC.Adv) = {
  module Game = DKC.Game(DKC.Dkc, Adv)
  fun work() : bool = {
    var r : bool;
    Adv.preInit();
    r = Game.work();
    return r;
  }
}.

module DkcWork(Adv:DKC.Adv) : MeanBool.Worker = {
  module Game = DKC.Game(DKC.Dkc, Adv)
  fun work(x:bool) : bool = {
    var r : bool;
    DKC.Dkc.b = x;
    Adv.preInit();
    r = Game.work();
    return r;
  }
}.

lemma DkcExp : forall (M<:DKC.Exp),
  equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}].
proof.
intros _;fun true;progress assumption.
save.


lemma DkcWork :
  forall b,
  forall &m,
    forall (Adv<:DKC.Adv {DKC.Dkc, DKC.Game}),
      DKC.Dkc.b{m} = b =>
  Pr[DkcWorkAdv(Adv).work()@ &m:res] = 
    Pr[DkcWork(Adv).work(b)@ &m:res].
proof.
  intros b &m Adv h.
  cut eq : equiv[DkcWorkAdv(Adv).work ~ DkcWork(Adv).work
: DKC.Dkc.b{1} = x{2} /\ (glob Adv){1} = (glob Adv){2} /\ (glob DKC.Game(DKC.Dkc,Adv)){1} = (glob DKC.Game(DKC.Dkc,Adv)){2}
      ==>res{1}=res{2}].
  fun.
  call ((glob DKC.Game(DKC.Dkc,Adv)){1} = (glob DKC.Game(DKC.Dkc,Adv)){2}) (res{1}=res{2}).
  apply (DkcExp (<:DKC.Game(DKC.Dkc,Adv))).
  call ((glob Adv){1} = (glob Adv){2}) (res{1}=res{2}/\(glob Adv){1} = (glob Adv){2}).
  fun true;progress assumption.
  wp.
  skip;progress.
  equiv_deno eq;progress assumption.
save.

theory AdvEsp.

op b : bool.

module AdvWork(Adv:Garble.Adv) : MeanInt.Worker = {
  module Game = DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))

  fun work(x:int) : bool = {
    var r : bool;
    AdvGarble.Adv.l = x;
    DKC.Dkc.b = b;
    r = Game.work();
    return r;
  }
}.

lemma AdvEsp :
  forall &m,
    forall (Adv<:Garble.Adv{DKC.Dkc,AdvGarble.Adv,DKC.Game}),
      forall c, c = b =>
      Pr[DkcWork(AdvGarble.Adv(Adv)).work(c)@ &m:res] =
        (sum (lambda l, (1%r / (borne + 1)%r) * Pr[AdvWork(Adv).work(l)@ &m:res]) MeanInt.support).
proof.
  intros &m Adv c h.
  cut pr : (Pr[MeanInt.Rand(AdvWork(Adv)).randAndWork()@ &m:res] = Pr[DkcWork(AdvGarble.Adv(Adv)).work(c)@ &m:res]).
    cut eq : equiv[
      MeanInt.Rand(AdvWork(Adv)).randAndWork ~
      DkcWork(AdvGarble.Adv(Adv)).work: x{2} = c /\ (glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){1}=(glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){2}
      ==>res{1}=res{2}].
      fun.
      inline AdvGarble.Adv(Adv).preInit.
      inline AdvWork(Adv).work.
      wp.
      call ((glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){1}=(glob DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv))){2}) (res{1}=res{2}).
      apply (DkcExp (<:DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv)))).
      wp.
      rnd.
      wp.
      skip. progress assumption.
    equiv_deno eq;progress assumption;trivial.
  rewrite <- pr.

rewrite (sum_in<:int> (lambda (l : int), (1%r / (borne + 1)%r) * Pr[AdvWork(Adv).work(l) @ &m : res{hr}]) MeanInt.support).
simplify.
cut lem : ((lambda (x:int),
(if mem x MeanInt.support then
  1%r / (Int.(+) borne 1)%r * Pr[AdvWork(Adv).work(x) @ &m : res{hr}]
else
  0%r)) = lambda (x:int), (mu_x MeanInt.d x * Pr[AdvWork(Adv).work(x) @ &m :res{hr}])).
delta MeanInt.d.
apply (Fun.extensionality<:real, int> (lambda (x:int),
(if mem x MeanInt.support then
  1%r / (Int.(+) borne 1)%r * Pr[AdvWork(Adv).work(x) @ &m : res{hr}]
else
  0%r)) (lambda (x:int), (mu_x MeanInt.d x * Pr[AdvWork(Adv).work(x) @ &m :res{hr}])) _).
intros x.
case (mem x MeanInt.support = true);last trivial.
intros hh.
delta MeanInt.d.
rewrite (Dinter.mu_x_def_in 0 borne x _);first trivial.
rewrite (_:borne - 0 + 1 = borne + 1);first trivial.
rewrite hh.
progress.
rewrite lem.
apply (MeanInt.Mean &m (<:AdvWork(Adv))).
save.

end AdvEsp.

clone AdvEsp as AdvEspTrue with op b = true.
clone AdvEsp as AdvEspFalse with op b = false.

lemma DkcEsp :
  forall &m,
    forall (Adv<:DKC.Adv {DKC.Dkc, DKC.Game}),
      Pr[DKC.Game(DKC.Dkc, Adv).main()@ &m:res] = 
        (Pr[DkcWork(Adv).work(true)@ &m:res] +
           Pr[DkcWork(Adv).work(false)@ &m:res]) / 2%r.
proof.
  intros &m Adv.
  cut pr : (Pr[DKC.Game(DKC.Dkc, Adv).main()@ &m:res] = Pr[MeanBool.Rand(DkcWork(Adv)).randAndWork()@ &m:res]).
    cut eq : equiv[
      DKC.Game(DKC.Dkc, Adv).main ~
      MeanBool.Rand(DkcWork(Adv)).randAndWork: (glob Adv){1} = (glob Adv){2}/\ (glob DKC.Game(DKC.Dkc, Adv)){1}=(glob DKC.Game(DKC.Dkc, Adv)){2}
      ==>res{1}=res{2}].
      fun.
      inline DKC.Game(DKC.Dkc, Adv).preInit.
      inline DKC.Dkc.preInit.
      inline DkcWork(Adv).work.
      wp.
      cut prelem : (forall (M<:DKC.Exp), equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}]);
        first (intros M;fun true;by progress).
      call ((glob DKC.Game(DKC.Dkc, Adv)){1}=(glob DKC.Game(DKC.Dkc, Adv)){2}) (res{1}=res{2});
        first apply (prelem (<:DKC.Game(DKC.Dkc, Adv))).
      wp.
      call ((glob Adv){1} = (glob Adv){2}) ((glob Adv){1} = (glob Adv){2});first (fun true;by progress).
      wp;rnd;skip;by (progress assumption).
    equiv_deno eq;progress assumption;trivial.
  rewrite pr.
  rewrite (MeanBool.Mean &m (<:DkcWork(Adv))).
  delta MeanBool.support.
  rewrite (sum_add<:bool> (lambda (x : MeanBool.base),
     mu_x MeanBool.d x * Pr[DkcWork(Adv).work(x) @ &m : res{hr}]) (add true Set.empty) false _);first trivial.
  rewrite (sum_add<:bool> (lambda (x : MeanBool.base),
     mu_x MeanBool.d x * Pr[DkcWork(Adv).work(x) @ &m : res{hr}]) Set.empty true _);first trivial.
  rewrite (sum_nil<:bool> (lambda (x : MeanBool.base),
     mu_x MeanBool.d x * Pr[DkcWork(Adv).work(x) @ &m : res{hr}])).
  simplify.
  delta MeanBool.d.
  rewrite (Dbool.mu_x_def false).
  rewrite (Dbool.mu_x_def true).
  generalize Pr[DkcWork(Adv).work(false) @ &m : res{hr}].
  generalize Pr[DkcWork(Adv).work(true) @ &m : res{hr}].
  trivial.
save.

lemma RelDkcGarble :
  forall &m,
    forall (Adv<:Garble.Adv{DKC.Dkc,DKC.Game,AdvGarble.Adv}),
      Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] =
        2%r * borne%r * Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv)).main()@ &m:res]
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
       1%r / (Int.(+) borne 1)%r *
       Pr[AdvEspTrue.AdvWork(Adv).work(l) @ &m : res{hr}]) = lambda (l : int),
       1%r / (Int.(+) borne 1)%r * (f l));
    first (apply extensionality;delta (==);simplify;intros l;rewrite (fv l);split).
(**End Remove Pr*)

(**Remove Pr*)
  cut introG : (exists (g:int->real), (forall (l:int), (g l) =
    Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}]));first
    (exists (lambda (l:int), Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}]);
     simplify;split).
  elim introG.
  intros g gv.
  rewrite (_:(lambda (l : int),
       1%r / (Int.(+) borne 1)%r *
       Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}]) = lambda (l : int),
       1%r / (Int.(+) borne 1)%r * (g l));
    first (apply extensionality;delta (==);simplify;intros l;rewrite (gv l);split).
(**End Remove Pr*)

(**Remove Pr*)
cut valf0 : (f 0 = Pr[Game(PrvInd(RandGarble), Adv).main() @ &m : res{hr}]).
  admit.
rewrite <- valf0.
(**End Remove Pr*)

trivial.

  rewrite (sum_rm<:int>
   (lambda (l : int), 1%r / (Int.(+) borne 1)%r * (f l))
   MeanInt.support
   0 _);first trivial.
  rewrite (sum_rm<:int>
   (lambda (l : int), 1%r / (Int.(+) borne 1)%r * (g l))
   MeanInt.support
   borne _);first trivial.
trivial.
rewrite ( _ :
(lambda (l : int), 1%r / (Int.(+) borne 1)%r * (f l)) 0 +
sum (lambda (l : int), 1%r / (Int.(+) borne 1)%r * (f l)) (rm 0 MeanInt.support) +
((lambda (l : int), 1%r / (Int.(+) borne 1)%r * (g l)) borne +
sum (lambda (l : int), 1%r / (Int.(+) borne 1)%r * (g l)) (rm borne MeanInt.support))
=
(lambda (l : int), 1%r / (Int.(+) borne 1)%r * (g l)) borne +
(lambda (l : int), 1%r / (Int.(+) borne 1)%r * (f l)) 0 +
(sum (lambda (l : int), 1%r / (Int.(+) borne 1)%r * (f l)) (rm 0 MeanInt.support) +
sum (lambda (l : int), 1%r / (Int.(+) borne 1)%r * (g l)) (rm borne MeanInt.support))

);trivial.

  rewrite (sum_chind<:int>
    (lambda (l : int),
       1%r / (Int.(+) borne 1)%r *
       Pr[AdvEspTrue.AdvWork(Adv).work(l) @ &m :res{hr}])
    (lambda (x:int), x - 1)
    (lambda (x:int), x + 1)
    (rm 0 MeanInt.support) _);first trivial.
  simplify.
  rewrite (_ : 
    (map (lambda (x : int), x-1) (rm 0 MeanInt.support)) =
    (rm borne MeanInt.support)
    ).
  delta MeanInt.support.
  apply (Induction.induction
(lambda i, map (lambda (x : int), Int.(-) x 1) (rm 0 (integers 0 i)) =
rm i (integers 0 i)) _ _ borne _);trivial.

  rewrite (sum_add<:int>
    (lambda (l : int),
       1%r / (Int.(+) borne 1)%r *
       Pr[AdvEspTrue.AdvWork(Adv).work((l + 1)) @ &m :res{hr}])
    (lambda (l : int),
       1%r / (Int.(+) borne 1)%r *
       Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m :res{hr}])
    (rm borne MeanInt.support)).
  simplify.
  admit.
(*
cut test : (forall l, Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : res{hr}] = 1%r - Pr[AdvEspFalse.AdvWork(Adv).work(l) @ &m : ! res{hr}]).
  apply (MeanInt.Not &m (<:AdvEspFalse.AdvWork(Adv))).

trivial.
  rewrite sum
  admit.*)
save.

lemma PrvIndGarble :
  exists (epsilon:real), epsilon > 0%r /\
    forall (Adv<:Garble.Adv {DKC.Dkc}), forall &m,
        `|Pr[Garble.Game(Garble.PrvInd(RandGarble), Adv).main()@ &m:res] - 1%r / 2%r| < epsilon.
proof.
  elim DKC.Security.
  intros epDkc hDkc.
  elim hDkc. clear hDkc.
  intros hPos hDkc.
  exists (borne%r*epDkc).
  cut bPos : (borne%r > 0%r).
  trivial.
  progress.
  trivial.
  rewrite (RelDkcGarble &m (<:Adv)).
  cut remPr : (forall (x:real), `|2%r * x - 1%r| < epDkc => `|2%r * borne%r * x +
  1%r / 2%r - borne%r - 1%r / 2%r| < borne%r * epDkc).
    intros x h.
    rewrite (_:`|2%r * borne%r * x + 1%r / 2%r - borne%r - 1%r / 2%r| = `|2%r * x - 1%r| * `| borne%r|);first trivial.
  rewrite (_:(`|borne%r| = borne%r));first trivial.
  apply (simpl (`|2%r * x - 1%r|) (borne%r) epDkc);assumption.
  apply (remPr Pr[DKC.Game(DKC.Dkc, AdvGarble.Adv(Adv)).main() @ &m :res{hr}] _).
  apply (hDkc (<:AdvGarble.Adv(Adv)) &m).
save.



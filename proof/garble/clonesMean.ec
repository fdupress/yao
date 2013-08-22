require import FSet. import Interval.
require ISet.
require import Int.
require import Bool.
require import Distr.
require import Real.

require import Mean.
require import Monoid. import Mrplus.

require import PreProof.
require import ReductionAda.

lemma DkcExp : forall (M<:DKCS.Exp),
  equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}]
by (intros _;fun true;progress assumption).

clone Mean as MeanBool with
  type base = bool,
  op d = Dbool.dbool.
op suppBool = add false (add true FSet.empty).
lemma suppBool : forall x, in_supp x MeanBool.d <=> mem x suppBool
  by (intros=> x;rewrite /suppBool /MeanBool.d ! mem_add Dbool.supp_def;case x=> ? //).
lemma mem_suppBool : forall x, ISet.mem x (ISet.support MeanBool.d) <=> mem x suppBool
  by (intros x;rewrite /ISet.support ISet.mem_create /= suppBool //).
lemma suppBoolF : ISet.Finite.finite (ISet.support (MeanBool.d))
  by (exists suppBool=> x;rewrite /ISet.Finite.finite mem_suppBool //).
lemma suppBoolV : ISet.Finite.toFSet (ISet.support (MeanBool.d)) = suppBool.
proof strict.
  apply set_ext=> x.
  rewrite ISet.Finite.mem_toFSet;
    first by apply suppBoolF.
  rewrite mem_suppBool //.
qed.


clone Mean as MeanInt with
  type base = int,
  op d = Dinter.dinter 0 (Cst.bound-1).
op suppInt = interval 0 (Cst.bound-1).
lemma suppInt : forall x,in_supp x MeanInt.d <=> mem x suppInt
  by (intros=> x;rewrite /suppInt mem_interval /MeanInt.d Dinter.supp_def //).
lemma mem_suppInt : forall x, ISet.mem x (ISet.support MeanInt.d) <=> mem x suppInt
  by (intros x;rewrite /ISet.support ISet.mem_create /= suppInt //).
lemma suppIntF : ISet.Finite.finite (ISet.support (MeanInt.d))
  by  (exists suppInt=> x;rewrite /ISet.Finite.finite /ISet.support ISet.mem_create /= suppInt //).
lemma suppIntV : ISet.Finite.toFSet (ISet.support (MeanInt.d)) = suppInt.
proof strict.
  apply set_ext=> x.
  rewrite ISet.Finite.mem_toFSet;
    first by apply suppIntF.
  rewrite mem_suppInt //.
qed.

module DkcWork(Adv:DKCS.AdvAda_t) : MeanBool.Worker = {
  module Game = DKCS.GameAda(DKCS.Dkc, Adv)
  module ADV = Adv(DKCS.Dkc)
  fun work(x:bool) : bool = {
    var r : bool;
    DKCS.Dkc.b = x;
    ADV.preInit();
    r = Game.work();
    return r;
  }
}.

module DkcWorkAdv(Adv:DKCS.AdvAda_t) = {
  module Game = DKCS.GameAda(DKCS.Dkc, Adv)
  module ADV = Adv(DKCS.Dkc)
  fun work() : bool = {
    var r : bool;
    ADV.preInit();
    r = Game.work();
    return r;
  }
}.

lemma DkcWork :
  forall b,
  forall &m,
    forall (Adv<:DKCS.AdvAda_t {DKCS.Dkc, DKCS.Game}),
      DKCS.Dkc.b{m} = b =>
  Pr[DkcWorkAdv(Adv).work()@ &m:res] = 
    Pr[DkcWork(Adv).work(b)@ &m:res].
proof strict.
  intros b &m Adv h.
  cut eq : equiv[DkcWorkAdv(Adv).work ~ DkcWork(Adv).work
: DKCS.Dkc.b{1} = x{2} /\ (glob Adv){1} = (glob Adv){2} /\ (glob DKCS.GameAda(DKCS.Dkc,Adv)){1} = (glob DKCS.GameAda(DKCS.Dkc,Adv)){2}
      ==>res{1}=res{2}];
  last equiv_deno eq;progress assumption.
  fun.
  call (DkcExp (DKCS.GameAda(DKCS.Dkc, Adv))).
  call (_:
    (glob Adv){1} = (glob Adv){2} ==>
    (res{1}=res{2}/\(glob Adv){1} = (glob Adv){2})).
  fun true;progress assumption.
  wp.
  skip;progress.
save.

lemma DkcEsp :
  forall &m,
    forall (Adv<:DKCS.AdvAda_t {DKCS.Dkc, DKCS.Game, MeanBool.Rand}),
      Pr[DKCS.GameAda(DKCS.Dkc, Adv).main()@ &m:res] = 
        (Mrplus.Base.(+) Pr[DkcWork(Adv).work(true)@ &m:res]
           Pr[DkcWork(Adv).work(false)@ &m:res]) / 2%r.
proof strict.
  intros &m Adv.
  cut pr : (Pr[DKCS.GameAda(DKCS.Dkc, Adv).main()@ &m:res] = Pr[MeanBool.Rand(DkcWork(Adv)).randAndWork()@ &m:res]).
    cut eq : equiv[
      DKCS.GameAda(DKCS.Dkc, Adv).main ~
      MeanBool.Rand(DkcWork(Adv)).randAndWork: (glob Adv){1} = (glob Adv){2}/\ (glob DKCS.GameAda(DKCS.Dkc, Adv)){1}=(glob DKCS.GameAda(DKCS.Dkc, Adv)){2}
      ==>res{1}=res{2}].
      fun.
      inline DKCS.GameAda(DKCS.Dkc, Adv).preInit.
      inline DKCS.Dkc.preInit.
      inline DkcWork(Adv).work.
      wp.
      cut prelem : (forall (M<:DKCS.Exp), equiv[M.work~M.work:(glob M){1}=(glob M){2}==>res{1}=res{2}]);
        first (intros M;fun true;by progress).
      call (prelem (DKCS.GameAda(DKCS.Dkc, Adv))).
      call (_:(glob Adv){1} = (glob Adv){2} ==> (glob Adv){1} = (glob Adv){2});first (fun true;by progress).
      wp;rnd;skip;by (progress assumption).
    equiv_deno eq;progress assumption;smt.
  rewrite pr (MeanBool.Mean &m (DkcWork(Adv)));first by apply suppBoolF.
  (rewrite suppBoolV /suppBool ! sum_add;first rewrite mem_add /=);first 2 apply mem_empty.
  simplify MeanBool.d.
  rewrite sum_empty ! Dbool.mu_x_def.
  smt.
save.

theory RedEsp.

  op b : bool.

  module RedWork(Adv:PrvIndSec.Adv_t) : MeanInt.Worker = {
    module Game = DKCS.GameAda(DKCS.Dkc, RedAda(Adv))

    fun work(x:int) : bool = {
      var r : bool;
      RedAda.l = x;
      DKCS.Dkc.b = b;
      r = Game.work();
      return r;
    }
  }.

lemma RemRedEsp : forall (p:bool -> bool) (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc}) &1 &2 l,
  (glob DKCS.GameAda){1} = (glob DKCS.GameAda){2} =>
  (glob RedAda){1} = (glob RedAda){2}=>
  (glob ADV){1} = (glob ADV){2}=>
  Pr[RedWork(ADV).work(l)@ &1:p res] = Pr[PreInit(ADV).f(l, b)@ &2:p res].
proof strict.
(*Proof correct but take a lot of useless time*)
intros=> ? ? ? ? ? ? ? ?;
(equiv_deno(_: ={glob DKCS.GameAda,glob RedAda,glob ADV}/\
              x{1}=vl{2}/\b=vb{2} ==> ={res});
  first fun;call (DkcExp (DKCS.GameAda(DKCS.Dkc, RedAda(ADV))));wp;skip);
  progress assumption.
save.

lemma AdvEsp :
  forall &m,
    forall (ADV<:PrvIndSec.Adv_t{DKCS.Dkc,RedAda,DKCS.Game,MeanInt.Rand}),
      Pr[DkcWork(RedAda(ADV)).work(b)@ &m:res] =
        (sum (lambda l, (1%r / Cst.bound%r) * Pr[RedWork(ADV).work(l)@ &m:res]) suppInt).
proof strict.
  intros &m ADV.
  cut <- : (Pr[MeanInt.Rand(RedWork(ADV)).randAndWork()@ &m:res] = Pr[DkcWork(RedAda(ADV)).work(b)@ &m:res]).
    equiv_deno (_:x{2} = b /\ (glob DKCS.GameAda(DKCS.Dkc, RedAda(ADV))){1}=(glob DKCS.GameAda(DKCS.Dkc, RedAda(ADV))){2} ==>res{1}=res{2})=> //.
      fun.
      inline DkcWork(RedAda(ADV)).ADV.preInit RedWork(ADV).work.
      wp.
      call (DkcExp (DKCS.GameAda(DKCS.Dkc, RedAda(ADV)))).
      wp;rnd;wp;skip;progress assumption.
rewrite sum_in.
simplify.
cut -> : ((lambda (x:int),
(if mem x suppInt then Pr[RedWork(ADV).work(x) @ &m : res{hr}]/Cst.bound%r else
  Z)) = lambda (x:int), (mu_x MeanInt.d x * Pr[RedWork(ADV).work(x) @ &m :res{hr}]));
last rewrite -suppIntV;apply (MeanInt.Mean &m (RedWork(ADV)));apply suppIntF.
apply fun_ext=> x /=.
case (mem x suppInt = true);
  [|rewrite rw_eqT -rw_neqF];
  intros=> memX;rewrite memX /=;
  rewrite /MeanInt.d;
  [rewrite Dinter.mu_x_def_in|rewrite Dinter.mu_x_def_notin];
  (try by rewrite - /MeanInt.d MeanInt.in_support memX //);smt.
save.

lemma RedEspT : forall x &m (ADV<:PrvIndSec.Adv_t{DKCS.Dkc,RedAda,DKCS.Game}),
  Pr[RedWork(ADV).work(x) @ &m : true] = 1%r.
proof strict.
intros x &m ADV.
bdhoare_deno (_: true ==> true)=> //.
fun.
admit.
save.

end RedEsp.

clone RedEsp as RedEspTrue  with op b = true.
clone RedEsp as RedEspFalse with op b = false.
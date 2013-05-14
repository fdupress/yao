require import Real.
require import Bool.
require import Logic.
require import Map.
require import Array.

require import Dkc.
require import Gate.
require import GarbleTools.
require AdvGate.

op opQuery : Gate.query.
op opB : bool.
module Adv : Gate.Adv = {
  fun gen_query() : Gate.query = {return opQuery;}
  fun get_challenge(answer:Gate.answer) : bool = {return opB;}
}.

lemma realEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
        Gate.Game(Gate.PrvInd, Adv).main :
      (Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0)
      ==> res{1} = res{2}
    ]
proof.
admit.
save.

lemma middleEq :
  forall &mDkc1,
    forall &mDkc2,
      forall (Adv <: Gate.Adv),
        equiv [
          Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
            Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
          (!Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) /\
          (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{1}=1)
          ==> !res{1} = res{2}
        ]
proof.
  intros &m1 &m2 Adv.
  fun.

  call (AdvGate.Adv.l{1}=0/\AdvGate.Adv.l{2}=1) (res{1}=res{2}).
    fun.
    call (answer{1}=answer{2}) (res{1}=res{2});[admit(*ADV rule*)|intros ch1 ch2].
    wp.
    app 1 2 : (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\AdvGate.Adv.g{1}=AdvGate.Adv.g{2}/\AdvGate.Adv.l{1}=0/\AdvGate.Adv.l{2}=1).
    rcondf {2} 1;[intros &m;skip;trivial|].
    rcondt {1} 1;[intros &m;skip;trivial|].
    rcondt {2} 1;[intros &m;skip;trivial|].
    call (true) (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\AdvGate.Adv.g{1}=AdvGate.Adv.g{2}).
      fun.
      wp.
      call (true) (
       (* (
          (AdvGate.Adv.g{2}.[( (AdvGate.get AdvGate.Adv.xc{2} 0)^^(proj (AdvGate.Adv.t{2}.[0])),  AdvGate.Adv.tau{2})] = hd answers{2}) /\
          (AdvGate.Adv.g{1}.[(tau,  t2)] = r0) /\
          (AdvGate.Adv.g{1}.[(tau, !t2)] = r1)
        ) => AdvGate.Adv.g{1}=AdvGate.Adv.g{2} *)
        AdvGate.Adv.input{1} = AdvGate.Adv.input{2}
      ).
      fun.
      call (false) (AdvGate.get AdvGate.Adv.input{1} 1 = AdvGate.get AdvGate.Adv.input{2} 1).
        fun.
        simplify.
        wp.
        skip.




    intros _ _.
    skip.
    trivial.
    rcondf {1} 1;[intros &m;skip;trivial|].
    rcondf {1} 1;[intros &m;skip;trivial|].
    rcondf {2} 1;[intros &m;skip;trivial|].
    skip.
    intros &1 &2 h.
    split.
    cut lem : (forall b1 b2,
      proj AdvGate.Adv.g{1}.[(b1, b2)] = proj AdvGate.Adv.g{1}.[(b1, b2)]).
    trivial.
    trivial.
    trivial.

call
  ((!Dkc.Dkc.b{1} = Dkc.Dkc.b{2}))
  (!res{1} = res{2}).
  fun.
  skip.
  trivial.
intros resultDkc_L resultDkc_R.
while (true).
  wp.
  call (true) (res{1} = res{2}).
    admit.
  admit.
  wp.
  app 1 1 : (true).
    call (true) (true).
      fun.
      rnd.
      skip.
      trivial.
    intros result_L0 result_R0.
    skip.
    trivial.
    admit. (*Call adv*)
admit. (*
call
  (true)
  (res{1} = res{2}).
  fun.
  skip.
  trivial.*)
save.

module RandBit = {
  fun main() : bool = {
    var b : bool;
    b = $Dbool.dbool;
    return b;
  }
}.
axiom RandBit : forall &m,
      Pr[RandBit.main()@ &m:res] = 1%r / 2%r.

lemma fakeEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ RandBit.main :
      (! Dkc.Dkc.b{1}) (*/\ (AdvGate.Adv.l{1}=1)*) ==> res{1} = res{2}
    ]
proof.
admit.
save.

(*
lemma real :
  forall &mDkc,(*forced b to 1 and l to 0*)
    forall &mGate,
      forall (Adv <: Gate.Adv),
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc:(*b /\ l=0 /\*) res] =
          Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGate:res]
proof.
admit.
save.

lemma middle :
  forall &mDkc1,(*forced b to 0 and l to 0*)
    forall &mDkc2,(*forced b to 1 and l to 1*)
      forall (Adv <: Gate.Adv),
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc1: !res] =
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDkc2:  res]
proof.
admit.
save.

module RandBit = {
  fun main() : bool = {
    var b : bool;
    b = $Dbool.dbool;
    return b;
  }
}.
axiom RandBit : forall &m,
      Pr[RandBit.main()@ &m:res] = 1%r / 2%r.

lemma fakeEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ RandBit.main :
      (! Dkc.Dkc.b) /\ (AdvGate.Adv.l=1) ==> res{1} = res{2}
    ]
proof.
intros Adv.
fun.
admit.
save.

lemma fake :
  forall &m,(*forced b to 0 and l to 1*)
  forall (Adv <: Gate.Adv),
      Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m: (!Dkc.Dkc.b)/\(*(AdvGate.Adv.l=1)/\*)(!res)] = 1%r / 2%r
proof.
intros &m Adv.
rewrite (RandBit &m).
equiv_deno (fakeEq Adv).
save.*)

lemma DkcAdvantage :
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
  forall &mDKC1,
  forall &mDKC0,
    2%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:res] - 1%r =
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC1:Dkc.Dkc.b/\res] -
    Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC0: !(Dkc.Dkc.b\/res)]
proof.
admit.
save.

lemma DkcTrue :
  forall (b:bool),
  forall (ADVDKC<:Dkc.Adv),
  forall &mDKC,
    3%r * Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:Dkc.Dkc.b/\res] =
     Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:(Dkc.Dkc.b^^b)/\(res^^b) (*/\ (AdvGate.Adv.l{1}=0)*)] +
     Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:(Dkc.Dkc.b^^b)/\(res^^b) (*/\ (AdvGate.Adv.l{1}=1)*)] +
     Pr[Dkc.Game(Dkc.Dkc, ADVDKC).main()@ &mDKC:(Dkc.Dkc.b^^b)/\(res^^b) (*/\ (AdvGate.Adv.l{1}=2)*)]
proof.
admit.
save.

lemma DkcGateRelation1 :
  forall &mDKC,
    forall (Adv<:Gate.Adv),
    forall &mGAR,
      2%r * Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] - 1%r
        =
      (2%r * Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGAR:res] - 1%r ) / 6%r
proof.
admit.
save.

lemma DKCGateRelation2 :
  forall &mDKC,
    forall (Adv <:Gate.Adv),
    forall &mGAR,
      Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGAR:res] <=
        Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res]
proof.
admit.
save.

lemma PrvIndGarble :
  forall (epsilon:real),
    forall (ADV<:Gate.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd, ADV).main()@ &m:res] <= epsilon
proof.
intros epsilon ADV &m.
intros epPos.
cut trans : (forall (a b c : real), a <= b => b <= c => a <= c);[trivial|].
apply (trans Pr[Gate.Game(Gate.PrvInd, ADV).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(ADV)).main()@ &m:res] epsilon _ _).
apply (DKCGateRelation2 &m ADV &m Pr[Gate.Game(Gate.PrvInd, ADV).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(ADV)).main()@ &m:res]).
admit.
save.
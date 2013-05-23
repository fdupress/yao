require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.

require import Dkc.
require import Gate.
require import GarbleTools.
require AdvGate.


lemma map : (forall (m:('a, 'b) map, x:'a, y:'b), proj m.[x <- y].[x] = y).

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
      forall (Adv <: Gate.Adv),
        equiv [
          Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
            Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
          (!Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) /\
          (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{1}=1)
          ==> !res{1} = res{2}
        ]
proof.
  intros Adv.
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


cut intro : (
          let preG_1 = AdvGate.Adv.preG{m1} in
          let preG_2 = AdvGate.Adv.preG{m2} in
          let g_1 = AdvGate.Adv.g{m1} in
          let g_2 = AdvGate.Adv.g{m2} in
          let fc = AdvGate.Adv.fc{m2} in
          let tau = AdvGate.Adv.tau{m2} in
          let x = AdvGate.Adv.x{m2} in
          let vis1 = (AdvGate.get AdvGate.Adv.xc{m2} 0)^^(proj AdvGate.Adv.t{m2}.[0]) in
equiv [AdvGate.Adv(Adv).computeG1 ~ AdvGate.Adv(Adv).computeG2 : (*&t1=&1/\&t2=&2*) true ==> AdvGate.Adv.input {1} =
  AdvGate.Adv.input {2} /\
  AdvGate.Adv.g {1} = AdvGate.Adv.g {2}]
);[|apply intro].
      
      intros preG1 preG2 g_1 g_2 fc tau x vis1.
      fun.
      wp.
      call (AdvGate.Adv.fc{1}=AdvGate.Adv.fc{2}/\AdvGate.Adv.xc{1}=AdvGate.Adv.xc{2}/\
        AdvGate.Adv.x{1}=AdvGate.Adv.x{2}/\ AdvGate.Adv.t{1}=AdvGate.Adv.t{2}/\
        AdvGate.Adv.g{1}=AdvGate.Adv.g{2}/\AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\(          if vis1 = tau then
            forall b, proj preG1.[(!vis1, b)] = proj preG2.[(!vis1, b)]
          else
            proj preG1.[(vis1, !tau)] = proj preG2.[(!vis1, !tau)])
        )
        (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\(
          if vis1 = tau then
            (forall b, proj g_1.[(!vis1, b)] = proj g_2.[(!vis1, b)]) /\
            proj g_1.[(vis1,   !tau)] = AdvGate.enc x preG1 fc vis1 (!tau)
          else
            proj g_1.[(vis1, !tau)] = proj g_2.[(!vis1, !tau)] /\
            proj g_1.[(vis1,  tau)] = AdvGate.enc x preG1 fc vis1 tau /\
            proj g_2.[(tau,  true)] = AdvGate.enc x preG2 fc tau true /\
            proj g_2.[(tau,  false)] = AdvGate.enc x preG2 fc tau false
        )).
  (*
          let g_1 = AdvGate.Adv.g{2} in
          let g_2 = AdvGate.Adv.g{2} in
          let tau = AdvGate.Adv.tau{2} in
          let xc = AdvGate.Adv.xc{2} in
          let x = AdvGate.Adv.x{2} in
          let t = AdvGate.Adv.t{2} in
          let x1 = get xc 0 in
          let x2 = get xc 1 in
          let t2 = proj t.[1] in
          let val0 = Gate.eval fc (!x1, false) in
          let val1 = Gate.eval fc (!x1, true) in
          let vis1 = x1^^(proj t.[0]) in
 *)
        fun.
        wp.
        skip.
        intros &1 &2 h.
        split.
        trivial.

        elim h; clear h; intros h1 h;
        elim h; clear h; intros h2 h;
        elim h; clear h; intros h3 h;
        elim h; clear h; intros h4 h;
        elim h; clear h; intros h5 h;
        elim h; clear h; intros h6.

        cut lem1 : (forall b1 b2, proj (Map.__get g_1 (b1, b2)) = AdvGate.enc AdvGate.Adv.x{1} preG1 AdvGate.Adv.fc{1} b1 b2). (*TODO*) admit.
        cut lem2 : (forall b1 b2, proj (Map.__get g_2 (b1, b2)) = AdvGate.enc AdvGate.Adv.x{2} preG1 AdvGate.Adv.fc{2} b1 b2). (*TODO*) admit.

        case (vis1 = tau).
        intros hvt h.



        split.
        intros b.
        rewrite (lem1 (!vis1) b).
        rewrite (lem2 (!vis1) b).
        delta AdvGate.enc.
        simplify.
        rewrite (_ : proj preG1.[(!vis1,  b)] = proj preG2.[(!vis1, b)]);[apply (h b)|trivial].
        rewrite (lem1 vis1 (!tau)).
        rewrite h1.
        rewrite h3.
        delta x fc.
        trivial.


          admit. (*TODO:*)
        split.
          admit. (*TODO:*)
        admit.
        intros hvt.
        split.
          admit. (*TODO:*)
        split.
          admit. (*TODO:*)
        admit.
      intros _ _.
        
        trivial.
      intros _ _.
      app 11 8 : true.
        call true true.
        fun.
        call true true.
        fun.
        wp.
    intros _ _.
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
save.*)

(*
lemma MiddleEq2 :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
      (! Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=1) /\ (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{2}=2) ==> res{1} = res{2}
    ]
proof.
intros Adv.
fun.
inline {1} Dkc.Dkc.preInit.
inline {1} Dkc.Dkc.get_challenge.
inline {1} Dkc.Dkc.initialize.
inline {1} AdvGate.Adv.gen_queries.
inline {1} AdvGate.Adv.get_challenge.
inline {2} Dkc.Dkc.preInit.
inline {2} Dkc.Dkc.get_challenge.
inline {2} Dkc.Dkc.initialize.
inline {2} AdvGate.Adv.gen_queries.
inline {2} AdvGate.Adv.get_challenge.
wp.
call (answer{1}=answer{2}) (res{1}=res{2}).
admit.
intros L R.
wp.
    rcondf {1} 8.
    intros &m.
    wp.

app 17 17 : (realChallenge{1}=realChallenge{2} /\ AdvGate.Adv.l{1}=1 /\ AdvGate.Adv.l{2}=2/\AdvGate.Adv.input{1}=AdvGate.Adv.input{2}).
  admit.
  app 2 3 : (realChallenge{1}=realChallenge{2} /\ AdvGate.Adv.l{1}=1 /\ AdvGate.Adv.l{2}=2/\AdvGate.Adv.g{1}=AdvGate.Adv.g{2}/\AdvGate.Adv.input{1}=AdvGate.Adv.input{2}).
    rcondf {1} 1;[intros &m;skip;trivial|].
    rcondt {1} 1;[intros &m;skip;trivial|].
    rcondf {2} 1;[intros &m;skip;trivial|].
    rcondf {2} 1;[intros &m;skip;trivial|].
    rcondt {2} 1;[intros &m;skip;trivial|].
    call (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}) (AdvGate.Adv.g{1}=AdvGate.Adv.g{2}/\AdvGate.Adv.input{1}=AdvGate.Adv.input{2}).
      fun.
      admit.
    intros L2 R2.
    skip.
    trivial.
  rcondf {1} 1;[intros &m;skip;trivial|].
  skip;intros _ _ _;split;trivial.
save.
*)

(*
lemma fakeEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ RandBit.main :
      AdvGate.Adv.l{1}=1 ==> res{1} = res{2}
    ]
proof.
intros Adv.
fun.
inline {1} Dkc.Dkc.preInit.
inline {1} Dkc.Dkc.get_challenge.
inline {1} Dkc.Dkc.initialize.

swap {1} 1 6.
swap {1} 9 -2.
wp.
(*Call magical function*)
save.*)

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
    forall (Adv<:Gate.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] <= epsilon
proof.
intros epsilon Adv &m.
intros epPos.
cut trans : (forall (a b c : real), a <= b => b <= c => a <= c);[trivial|].
(*apply (trans Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m:res] epsilon _ _).*)
apply (DKCGateRelation2 &m (<:Adv) &m  Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m:res]).
admit.
save.
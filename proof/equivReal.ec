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

lemma tr : true.

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

(*
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
    call (answer{1}=answer{2}) (res{1}=res{2});[admit(*ADV rule*)|].
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
  inline {1} AdvGate.Adv.gen_queries.
  rcondf {1} 7;[admit|].
  (*rcondf {1} 7. intros &m.
wp.
call true true.
  wp;try (call true true;[admit|]);try rnd .
  wp;try (call true true;[admit|]);try rnd .
  wp;try (call true true;[admit|]);try rnd .
  wp;try (call true true;[admit|]);try rnd .
call true true.*)

  rcondf {1} 8;[admit|].
  rcondt {1} 7;[admit|].
  rcondt {1} 12;[admit|].
  rcondf {1} 15;[admit|].
  inline {1} AdvGate.Adv.get_challenge.
  rcondf {1} 17;[admit|].
  rcondf {1} 18;[admit|].
  rcondt {1} 17;[admit|].
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGate.Adv.computeG2.
  inline {1} AdvGate.Adv.gen_queries2.
  inline {1} AdvGate.Adv.common0.
  inline {1} AdvGate.Adv.common1.
  inline {1} AdvGate.Adv.initX.
  inline {1} AdvGate.Adv.common2.
  inline {1} AdvGate.Adv.initPreG.
  inline {1} AdvGate.Adv.common3.

  inline {2} AdvGate.Adv.gen_queries.
  rcondf {2} 7;[admit|].
  rcondf {2} 7;[admit|].
  rcondt {2} 7;[admit|].
  rcondf {2} 12;[admit|].
  inline {2} AdvGate.Adv.get_challenge.
  rcondf {2} 14;[admit|].
  rcondf {2} 14;[admit|].
  rcondt {2} 14;[admit|].
  inline {2} Dkc.Dkc.preInit.
  inline {2} Dkc.Dkc.get_challenge.
  inline {2} Dkc.Dkc.initialize.
  inline {2} AdvGate.Adv.gen_queries3.
  inline {2} AdvGate.Adv.computeG3.
  inline {2} AdvGate.Adv.common0.
  inline {2} AdvGate.Adv.common1.
  inline {2} AdvGate.Adv.initX.
  inline {2} AdvGate.Adv.common2.
  inline {2} AdvGate.Adv.initPreG.
  inline {2} AdvGate.Adv.common3.

  wp.
  call (answer{1} = answer{2}) (res{1} = !res{2}). admit.
  wp.
  app 72 58 : (
    let xx1 = x1{1} in
    let xx2 = x2{1} in
    let vvis1 = vis1{1} in
    let tau = AdvGate.Adv.tau{1} in
    let input = AdvGate.Adv.input{1} in
    let g1 = AdvGate.Adv.g{1} in
    let g2 = AdvGate.Adv.g{2} in
    let preG1 = AdvGate.Adv.preG{1} in
    let preG2 = AdvGate.Adv.preG{2} in
    xx1 = x1{2} /\
    xx2 = x2{2} /\
    vvis1 = vis1{2} /\
    tau = AdvGate.Adv.tau{2} /\
    input = AdvGate.Adv.input{2} /\
    proj preG1.[(!vis1{1},  tau)]=proj preG2.[(!vis1{1},  tau)] /\
    proj preG1.[( vis1{1}, !tau)]=proj preG2.[( vis1{1}, !tau)] /\
    proj preG1.[( vis1{1},  tau)]=proj preG2.[( vis1{1},  tau)] /\
    proj g1.[(!vis1{1},  tau)]=proj g2.[(!vis1{1},  tau)] /\
    proj g1.[( vis1{1}, !tau)]=proj g2.[( vis1{1}, !tau)] /\
    proj g1.[(!vis1{1}, !tau)]=proj g2.[(!vis1{1}, !tau)] /\
    AdvGate.Adv.fc{1} = AdvGate.Adv.fc{2} /\
    realChallenge{1} = !realChallenge{2} ).
    rnd.

    wp.
    wp.
admit.

  if.

    intros &1 &2 h.
    rewrite (_:x1{1}=x1{2});[trivial|].
    rewrite (_:AdvGate.Adv.fc{1}=AdvGate.Adv.fc{2});[trivial|].
    simplify.
    apply tr.

    wp.
    skip.
    intros &1 &2 h.
    split.
    elim h; clear h; intros h h0;
    elim h; clear h; intros h1 h;
    elim h; clear h; intros h2 h;
    elim h; clear h; intros h3 h;
    elim h; clear h; intros h4 h;
    elim h; clear h; intros h5 h;
    elim h; clear h; intros h6 h;
    elim h; clear h; intros h7 h;
    elim h; clear h; intros h8 h;
    elim h; clear h; intros h9 h;
    elim h; clear h; intros h10 h;
    elim h; clear h; intros h11 h;
    elim h; clear h; intros h12 h13.
    rewrite h1;
    rewrite h2;
    rewrite h3;
    rewrite h4;
    rewrite h5;
    rewrite h6;
    rewrite h7;
    rewrite h8;
    rewrite h9;
    rewrite h10;
    rewrite h11;
    rewrite h12.
    simplify.
    admit.
    intros hh L R hhh.
    rewrite hhh.
    clear hhh hh.
    rewrite (_:realChallenge{1} = !realChallenge{2});[|clear h];trivial.

    rnd.
    skip.
    intros &1 &2 h x y.
    split.
    trivial.
    intros hh hhh.
    split.
    elim h; clear h; intros h h0;
    elim h; clear h; intros h1 h;
    elim h; clear h; intros h2 h;
    elim h; clear h; intros h3 h;
    elim h; clear h; intros h4 h;
    elim h; clear h; intros h5 h;
    elim h; clear h; intros h6 h;
    elim h; clear h; intros h7 h;
    elim h; clear h; intros h8 h;
    elim h; clear h; intros h9 h;
    elim h; clear h; intros h10 h;
    elim h; clear h; intros h11 h;
    elim h; clear h; intros h12 h13.
    rewrite h1;
    rewrite h2;
    rewrite h3;
    rewrite h4;
    rewrite h5;
    rewrite h6;
    rewrite h7;
    rewrite h8;
    rewrite h9;
    rewrite h10;
    rewrite h11;
    rewrite h12.
    simplify.
    admit.
    intros hhhh L R hhhhh.
    rewrite hhhhh.
    clear hhhhh hhhh hhh hh.
    rewrite (_:realChallenge{1} = !realChallenge{2});[|clear h]; trivial.

    


ssss
  rcondf {1} 8;[admit|].
  rcondf {1} 9;[admit|].
  rcondt {1} 8;[admit|].   
  rcondf {2} 8;[admit|].
  rcondf {2} 8;[admit|].
  rcondt {2} 8;[admit|].

  call (answer{1}=answer{2}) (res{1}=res{2}). admit.
    intros &m.
    wp.
rcondf {1} 1;[admit|].
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

lemma fakeEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
      AdvGate.Adv.l{1}=2 ==> res{1} = res{2}
    ]
proof.
  intros Adv.
  fun.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  rcondf {1} 7.
    intros &m.
    wp.
    call (AdvGate.Adv.l = 2) (List.length res = 0).
      fun.
      app 4 : (AdvGate.Adv.l = 2).
        wp.
        call (true) (true). admit.
        rnd.
        skip.
        trivial.
      rcondf 1;[skip;trivial|].
      rcondf 1;[skip;trivial|].
      rcondt 1;[skip;trivial|].
      call (true) (length res = 0). admit.
    skip. trivial.
    wp.
    rnd.
    skip.
    trivial.
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
intros &mDKC Adv &mGAR.
cut intro : (
let a = Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &mDKC:res] in
let b = Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &mGAR:res] in
a <= b).
intros a b.
cut lem : (2%r * a - 1%r = (2%r * b - 1%r ) / 6%r);
  [apply (DkcGateRelation1 &mDKC (<:Adv) &mGAR)|].
cut lem2 : (a = b / 6%r + 5%r / 12%r). trivial.
trivial.
trivial.
trivial.
save.

lemma PrvIndGarble :
  forall (epsilon:real),
    forall (Adv<:Gate.Adv), forall &m,
      epsilon > 0%r => Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] <= epsilon
proof.
intros epsilon Adv &m.
intros epPos.
cut trans : (forall (a b c : real), a <= b => b < c => a <= c);[trivial|].
apply (trans Pr[Gate.Game(Gate.PrvInd, Adv).main()@ &m:res] Pr[Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).main()@ &m:res] epsilon _ _).
apply (DKCGateRelation2 &m (<:Adv) &m).
apply (Dkc.DKCSec epsilon (<:AdvGate.Adv(Adv)) &m _).
trivial.
save.
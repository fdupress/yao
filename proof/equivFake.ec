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

require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.

require import Dkc.
require import Gate.
require import GarbleTools.

lemma FakeEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ AdvGate.Adv(Adv).fake :
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
  rcondf {1} 9;[admit|].
  rcondt {1} 9;[admit|].
  rcondf {1} 17;[admit|].
  rcondt {1} 17;[admit|].
  inline {1} AdvGate.Adv.compute1.
  inline {1} AdvGate.Adv.gen_queries1.
  rcondt {1} 15;[admit|].
  rcondf {1} 18;[admit|].
  inline {1} Dkc.Dkc.encrypt.

  wp.
  swap {2} 22 -20.
  call (answer{1}=answer{2}) (res{1} = res{2}). admit.
  wp.
  rnd.
  rnd.
  rnd.
  rnd.
  rcondf {1} 27. admit.
  rnd.
  wp.
  rcondt {1} 18. admit.
  wp.
  rcondt {1} 19. admit.
  rcondt {1} 20. admit.
  rcondt {1} 21. admit.
  rnd.
  rnd.
  rnd.
  wp.
  rnd.
  wp.
  call true (res{1} = res{2}). admit.
  rnd.
  wp.
  app 1 1 : ((! Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=1) /\ (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{2}=2)/\t{1} = t1{2}).
    rnd.
    skip.
    trivial.
  app 1 0 : ((! Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=1) /\ (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{2}=2)/\t{1} = t1{2}).
  admit.
  skip.
  simplify.
  intros &1 &2 h hh hhh.
  split.
  trivial.
  intros g gg L R ggggg.
  simplify.


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
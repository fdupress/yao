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

module Adv(A:Gate.Adv) : Dkc.Adv = {
    fun advgen_query() : Gate.query = {
      var r : query;
      return r;
    }
    fun advget_challenge(answer: Gate.answer) : bool = {
      var r : bool;
      return r;
    }

  var fc : Gate.funct
  var xc : Gate.input
  var tau : bool
  var l : int

  var input : Gate.inputG
  var g : ((bool*bool), token) map
  var preG : ((bool*bool), token) map
  var x : (int*bool, token) map
  var t : (int, bool) map

  fun common0() : unit = {
    x = Map.empty;
    preG = Map.empty;
    g = Map.empty;
    t = Map.empty;
    t.[0] = $Dbool.dbool;
    t.[1] = $Dbool.dbool;
    t.[2] = false;
  }

  fun initX(i:int, b:bool) : unit = {
    x.[(i, b)] = $Dkc.genRandKeyLast((proj t.[i])^^b);
  }
  fun common1() : unit = {
    initX(0, false);
    initX(0,  true);
    initX(1, false);
    initX(1,  true);
    initX(2, false);
    initX(2,  true);
  }

  fun initPreG(a:bool, b:bool) : unit = {
    preG.[(a, b)] = proj x.[(2, Gate.eval fc (a, b))];
  }
  fun common2() : unit = {
    initPreG(false, false);
    initPreG( true, false);
    initPreG(false,  true);
    initPreG( true,  true);
  }
  
  fun common3() : unit = {
    g = initG g x preG fc false false;
    g = initG g x preG fc false true;
    g = initG g x preG fc true false;
    g = initG g x preG fc true true;
    input = initInput input x xc 0;
    input = initInput input x xc 1;
  }

  fun gen_queries3() : Dkc.query list = {

    common0();

    common1();
    
    return [];
  }

  fun computeG3(answers:Dkc.answer list) : unit = {
    var x1 : bool = get xc 0;
    var x2 : bool = get xc 1;
    var vis1:bool = (get xc 0)^^(proj t.[0]);
    var vis2:bool = (get xc 1)^^(proj t.[1]);

    common2();

    preG.[( vis1,  vis2)] = $Dkc.genRandKeyLast((proj t.[2])^^(Gate.eval fc (vis1, vis2))];
    preG.[( vis1, !vis2)] = $Dkc.genRandKey;
    preG.[(!vis1,  vis2)] = $Dkc.genRandKey;
    preG.[(!vis1, !vis2)] = $Dkc.genRandKey;

    common3();
  }
  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 2;
  }

  fun gen_queries(info:bool) : Dkc.query list = {
    var c : bool;
    var query : Gate.query;
    var ret : Dkc.query list;
    c = $Dbool.dbool;
    query := advgen_query();
    tau = info;
    if (c) (fc, xc) = fst query; else (fc, xc) = snd query;
    gen_queries3();
    return ret;
  }
  
  fun get_challenge(answers:Dkc.answer list) : bool = {
    var challenge : bool;
    var gg : Gate.functG;
    computeG3(answers);
    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge := advget_challenge((gg, input, tt));
    return challenge;
  }
}.


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
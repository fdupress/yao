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

module Fake(Adv:Gate.Adv) = {
  fun fake() : bool = {
    var c : bool;
    var query : Gate.query;
    var ret : Dkc.query list;
    var challenge : bool;
    var gg : Gate.functG;
    var query0 : Gate.funct*Gate.input;
    var query1 : Gate.funct*Gate.input;
    var v : bool;

    var rand : bool;
    var ntau : bool;
    var t : bool;
    var keyt : token;
    var keynt : token;
    var keytau : token;
    var keyntau : token;
    var key_t_tau : token;
    var key_nt_ntau : token;
    var key_nt_tau : token;
    var key_t_ntau : token;

    var input : Gate.inputG;
    var g : ((bool*bool), token) map;

    (* t^^(fst xc) = t *)
    (* !tau = ntau *)

    ntau = $Dbool.dbool;
    keytau = $Dkc.genRandKeyLast(!ntau);

    query := AdvGate.A.gen_query();
    query0 = fst query;
    query1 = snd query;
    if (Gate.eval (fst query0) (snd query0) = Gate.eval (fst query0) (snd query0))
    {
    v = Gate.eval (fst query0) (snd query0);
    
    t = $Dbool.dbool;

    keyt = $Dkc.genRandKeyLast(t);
    key_t_tau = $Dkc.genRandKey;

    keynt = $Dkc.genRandKeyLast(!t);
    key_nt_tau = $Dkc.genRandKey;

    key_t_ntau = $Dkc.genRandKeyLast(v);

    keyntau = $Dkc.genRandKeyLast(ntau);
    key_nt_ntau  = $Dkc.genRandKey;

    input = (keyt, keyntau);
    
    g.[(  ntau,  t)] = Dkc.encode
      (tweak 2 ( ntau) ( t))
      keyntau
      keyt
      key_t_ntau;
    g.[(  ntau, !t)] = Dkc.encode
      (tweak 2 ( ntau) (!t))
      keyntau
      keynt
      key_nt_ntau;
    g.[( !ntau,  t)] = Dkc.encode
      (tweak 2 (!ntau) ( t))
      keytau
      keyt
      key_t_tau;
    g.[( !ntau,  !t)] = Dkc.encode
      (tweak 2 (!ntau) (!t))
      keytau
      keynt
      key_nt_tau;

    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge := AdvGate.A.get_challenge((gg, input, tt));
    }
    else
      challenge = $Dbool.dbool;
    c = $Dbool.dbool;
    return c = challenge;
  }
}.

lemma FakeEq :
  forall (Adv <: Gate.Adv),
    equiv [
      Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~ Fake(Adv).fake :
      (! Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=1) ==> res{1} = res{2}
    ]
proof.
  intros Adv.
  fun.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} AdvGate.Adv.gen_queries.
  inline {1} AdvGate.Adv.get_challenge.
  rcondf {1} 11;[admit|]. (* l condition *)
  rcondt {1} 11;[admit|]. (* l condition *)
  rcondf {1} 19;[admit|]. (* l condition *)
  rcondt {1} 19;[admit|]. (* l condition *)
  inline {1} AdvGate.Adv.compute1.
  inline {1} AdvGate.Adv.gen_queries1.
  rcondt {1} 18;[admit|]. (* While *)
  rcondt {1} 21;[admit|]. (* While *)
  rcondf {1} 24;[admit|]. (* While *)
  inline {1} Dkc.Dkc.encrypt.

  wp.
  swap {2} 7 -4.
  rcondt {2} 7. admit. (*FAUX*) (*BAD Condition*)
  call (answer{1}=answer{2}) (res{1} = res{2}). admit. (* Call Adv get_challenge *)
  wp.
  rnd. (* key_nt_ntau *)
  rnd. (* keyntau *)
  wp.
  rcondf {1} 37. admit. (*FAUX*) (* Reutilisation clef sortie *)
  rcondf {1} 37. admit. (*FAUX*) (* Reutilisation clef sortie *)
  rnd. (* key_t_ntau *)
  wp.

  (*BEGIN DKC*)
  (*LOOP 1*)
  rcondt {1} 28;[admit|]; (* Dkc used *)
  wp;
  rcondt {1} 29;[admit|]; (* Dkc not reusing *)
  rcondf {1} 30;[admit|]; (* Dkc not reusing *)
  rcondt {1} 30;[admit|]; (* Dkc not reusing *)
  rnd; (* key_nt_tau *)
  rnd; (* keynt *)
  wp;
  (*LOOP 2*)
  rcondt {1} 21;[admit|]; (* Dkc used *)
  wp;
  rcondt {1} 22;[admit|]; (* Dkc not reusing *)
  rcondf {1} 23;[admit|]; (* Dkc not reusing *)
  rcondt {1} 23;[admit|]; (* Dkc not reusing *)
  rnd; (* key_t_tau *)
  rnd; (* keyt *)
  wp;
  (*END DKC*)
  rnd {1}; (* rand *)
  rnd (lambda x, x^^(fst AdvGate.Adv.xc{1})) _; (* t *)
  wp;
  call true (res{1} = res{2});[admit|]; (* Call Adv gen_query *)
  rnd; (* c *)
  wp;
  rnd; (*keyTau*)
  rnd (lambda x, !x) _; (*tau*)

  skip;

  intros &1 &2 pre;
  simplify.
  intros tau1 ntau2;split;[trivial|];intros eqtau intau;
  intros keyTau1 keyTau2;split;[trivial|];intros eqKeyTau inKeyTau;
  intros c1 c2;split;[trivial|];intros eqc inc;
  intros query1 query2 eqQuery;
  case c1;[|admit];intros c1val;
    intros t1 t2; split;[trivial|];intros eqt int;
    intros rand inrand;

    (* UGLY *)
    rewrite (hd_def<:(int*bool)*(int*bool)*bool*(bool array)> ((0, t1 ^^ fst (snd (fst query1))),
    (1,
      eval (fst (fst query1)) (fst (snd (fst query1)),
        !snd (snd (fst query1)))),
      false, tweak 0 (!t1 ^^ (fst (snd (fst query1)))) tau1)
(
    (((0, !t1 ^^ fst (snd (fst query1))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1) ::
      __nil)));
    (* END UGLY *)

    simplify;
    intros keyt1 keyt2; split;[trivial|];intros eqkeyt inkeyt;
    intros key_t_tau inkey_t_tau;

    (* UGLY *)
    rewrite (tl_def<:(int*bool)*(int*bool)*bool*(bool array)> ((0, t1 ^^ fst (snd (fst query1))),
    (1,
      eval (fst (fst query1)) (fst (snd (fst query1)),
        !snd (snd (fst query1)))),
      false, tweak 0 (!t1 ^^ (fst (snd (fst query1)))) tau1)
(
    (((0, !t1 ^^ fst (snd (fst query1))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1) ::
      __nil)));
    rewrite (hd_def<:(int*bool)*(int*bool)*bool*(bool array)>
    ((0, !t1 ^^ fst (snd (fst query1))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1) __nil);
    (* END UGLY *)

    rewrite (_:Dkc.Dkc.b{1} = false);[trivial|];
    simplify;
    intros keynt1 keynt2; split;[trivial|];intros eqkeynt inkeynt;
    intros key_nt_tau inkey_nt_tau;

    (* UGLY *)

rewrite (hd_def<:Dkc.key*Dkc.key*Dkc.cipher>
(proj Map.empty.[(0,
    t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
    !t1 ^^ fst (snd (fst query1))) <- keynt1].[(0,
    !t1 ^^ fst (snd (fst query1)))],

    proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
      !t1 ^^ fst (snd (fst query1))) <- keynt1].[(2, rand)],

      Dkc.encode
        (tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1)
        (proj Map.empty
          .[(0,t1 ^^ fst (snd (fst query1))) <- keyt1]
          .[(0,!t1 ^^ fst (snd (fst query1))) <- keynt1]
          .[(0,!t1 ^^ fst (snd (fst query1)))]) 
        keyTau1
        (proj Map.empty.[(1, eval (fst (fst query1)) (fst (snd (fst query1)),
          !snd (snd (fst query1)))) <- key_t_tau]
        .[(2, rand) <- key_nt_tau]
        .[(2, rand)])
)

(

(proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
      t1 ^^ fst (snd (fst query1)))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (fst query1))) <- keyt1].[(1,
        eval (fst (fst query1)) (fst (snd (fst query1)),
          !snd (snd (fst query1))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1) (proj Map.empty.[(0,
          t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
          t1 ^^ fst (snd (fst query1)))]) keyTau1 (proj Map.empty.[(1,
          eval (fst (fst query1)) (fst (snd (fst query1)),
            !snd (snd (fst query1)))) <- key_t_tau].[(1,
          eval (fst (fst query1)) (fst (snd (fst query1)),
            !snd (snd (fst query1))))])) ::
      __nil));
    (* END UGLY *)
    simplify;
    (* UGLY *)

rewrite (tl_def<:Dkc.key*Dkc.key*Dkc.cipher>
(proj Map.empty.[(0,
    t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
    !t1 ^^ fst (snd (fst query1))) <- keynt1].[(0,
    !t1 ^^ fst (snd (fst query1)))],

    proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
      !t1 ^^ fst (snd (fst query1))) <- keynt1].[(2, rand)],

      Dkc.encode
        (tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1)
        (proj Map.empty
          .[(0,t1 ^^ fst (snd (fst query1))) <- keyt1]
          .[(0,!t1 ^^ fst (snd (fst query1))) <- keynt1]
          .[(0,!t1 ^^ fst (snd (fst query1)))]) 
        keyTau1
        (proj Map.empty.[(1, eval (fst (fst query1)) (fst (snd (fst query1)),
          !snd (snd (fst query1)))) <- key_t_tau]
        .[(2, rand) <- key_nt_tau]
        .[(2, rand)])
)

(

(proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
      t1 ^^ fst (snd (fst query1)))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (fst query1))) <- keyt1].[(1,
        eval (fst (fst query1)) (fst (snd (fst query1)),
          !snd (snd (fst query1))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1) (proj Map.empty.[(0,
          t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
          t1 ^^ fst (snd (fst query1)))]) keyTau1 (proj Map.empty.[(1,
          eval (fst (fst query1)) (fst (snd (fst query1)),
            !snd (snd (fst query1)))) <- key_t_tau].[(1,
          eval (fst (fst query1)) (fst (snd (fst query1)),
            !snd (snd (fst query1))))])) ::
      __nil));
rewrite (hd_def<:Dkc.key*Dkc.key*Dkc.cipher>

(proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
      t1 ^^ fst (snd (fst query1)))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (fst query1))) <- keyt1].[(1,
        eval (fst (fst query1)) (fst (snd (fst query1)),
          !snd (snd (fst query1))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (fst query1))) tau1) (proj Map.empty.[(0,
          t1 ^^ fst (snd (fst query1))) <- keyt1].[(0,
          t1 ^^ fst (snd (fst query1)))]) keyTau1 (proj Map.empty.[(1,
          eval (fst (fst query1)) (fst (snd (fst query1)),
            !snd (snd (fst query1)))) <- key_t_tau].[(1,
          eval (fst (fst query1)) (fst (snd (fst query1)),
            !snd (snd (fst query1))))])) 
      __nil);
    (* END UGLY *)

simplify;

    intros key_t_ntau1 key_t_ntau2; split;[trivial|];intros eqkey_t_ntau inkey_t_ntau;
    intros key_ntau inkey_ntau;
    intros key_nt_ntau inkey_nt_ntau;
    split.
    admit.
    intros h.
clear h.
    trivial.


 key_nt_ntau
  rnd. (* keyntau *)
  wp.
  rcondf {1} 37. admit. (*FAUX*) (* Reutilisation clef sortie *)
  rcondf {1} 37. admit. (*FAUX*) (* Reutilisation clef sortie *)
  key_t_ntau


simplify.


end proof what follow contains old stuff
  rcondf {1} 27. admit.
  rnd.
  wp.
  rcondt {1} 18. admit.
  wp.
  rcondt {1} 19. admit.
  rcondf {1} 20. admit.
  rcondt {1} 20. admit.
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
require import Bitstring.
require import List.
require import Map.
require import FSet.
require import Pair.
require import Real.
require import Int.
require import Bool.
require import Array.
require import Distr.

require import GarbleTools.
require import PreProof.
require import ReductionAda.

module Fake(A:PrvIndSec.Adv_t) = {

  var f1 : funct
  var x1 : input
  var ev : output
  var good : bool
  var tau : bool
  var queries : DKCS.query array
  var ans : DKCS.answer array
  var answer : functG*inputG*keyOutput
  var query : PrvIndSec.Scheme.plain*PrvIndSec.Scheme.plain

  var n : int
  var m : int
  var q : int
  var aa : w2g
  var bb : w2g
  var pp : token g2v
  var t : bool array
  var xx : tokens
  var randG : (int*bool*bool, token) map
  var a : int
  var b : int
  var i : int
  var g : int

(*DKC var*)
  var ksec : token
  var r : (int*bool, token) map
  var kpub : (int*bool, token) map
(*End DKC Var*)

  fun query(rand:bool, alpha:bool, bet:bool) : unit = {
    var ttt : token;
    var pos : bool;
    var input : int*bool;
    var output : int*bool;
    var ra : bool;
    var ki : token;
    var ko : token;
    var tok : token;
    var zz : token;
    var temp : token;

    ttt = tweak g (t.[a]^^alpha) (t.[b]^^bet);
    input = (a, (t.[a]^^alpha));

    (*DKC encrypt*)
        temp = $DKC.genRandKeyLast;
        if (! (in_dom input kpub)) {
          kpub.[input] = DKC.addLast temp (snd input);
        }
        tok = $DKC.genRandKey;
        ki = proj kpub.[input];
        zz = DKCS.DKC_Abs.encode ttt ki ksec tok;
    (*End DKC encrypt*)
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) zz;
    xx = setTok xx g alpha ki;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) (DKCS.DKC_Abs.encode
      (tweak g (t.[a]^^alpha) (t.[b]^^bet))
      (getTok xx a alpha)
      (getTok xx b bet)
      yy);
  }

  fun garbD(alpha:bool, bet:bool) : token = {
    var yy : token;
    yy = proj randG.[(g,alpha,bet)];
    garb(yy, alpha, bet);
    return yy;
  }

  fun preGarbD(alpha:bool, bet:bool) : unit = {
    var yy : token;
    randG.[(g,alpha,bet)] = $DKC.genRandKey;
  }

  fun garble() : unit = {
    var tok : token;
    var yyt : token;

    i = 0;
    while (i < n+q-m) {
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < n+q) {
      t.[i] = false;
      i = i + 1;
    }


    t.[Cst.bound-1] = !tau;

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      if (b = Cst.bound - 1) {
        query(false, false, true);
        query(true, true, true);
        preGarbD(true, false);
        tok = $DKC.genRandKeyLast;
        xx = setTok xx g true (DKC.addLast tok (! t.[g]));
        tok = $DKC.genRandKeyLast;
        xx = setTok xx g false (DKC.addLast tok (t.[g]));
      } else {
        preGarbD(false, true);
        preGarbD(true, true);
        preGarbD(true, false);
      }
      g = g + 1;
    }

    i = 0;
    while (i < n+q) {
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (! t.[i]);
      if (getTok xx i true = void /\ i <> Cst.bound - 1) {
        xx = setTok xx i true tok;
      }
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (t.[i]);
      if (getTok xx i false = void) {
        xx = setTok xx i false tok;
      }
      i = i + 1;
    }

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      garb(getTok xx g false, false, false);
      if (b <> Cst.bound - 1) {
        tok = garbD(false, true);
        tok = garbD(true, true);
        tok = garbD(true, false);
      } else {
        tok = garbD(true, false);
      }
      g = g + 1;
    }
    answer = ((getN f1, getM f1, getQ f1, getA f1, getB f1, pp), encrypt (Array.sub xx 0 (getN f1)) (Array.create (getN f1) false),tt);
  }

  fun work() : bool = {
    var challenge : bool;
    var c : bool;
    var ret : bool;
    var gg : bool g2v;

    query = A.gen_query();
  
    if (PrvIndSec.Scheme.queryValid query)
    {
      tau = $Dbool.dbool;
      ksec = $DKC.genRandKeyLast;
      ksec = DKC.addLast ksec tau;
      kpub = Map.empty;
      r = Map.empty;

      (f1, x1) = fst query;
      (n, m, q, aa, bb, gg) = f1;
      ev = GarbleCircuit.eval f1 x1;
      queries = Array.empty;
      t = Array.create (n+q) false;
      xx = Array.create (n+q) (void, void);
      pp = Array.create (n+q) (void, void, void, void);
      randG = Map.empty;
      garble();
      challenge = A.get_challenge(answer);
      c = $Dbool.dbool;
      ret = (c = challenge);
    }
    else
      ret = $Dbool.dbool;
    return ret = false;
  }

}.

prover "Alt-Ergo".

lemma garbL (ADV <: PrvIndSec.Adv_t): islossless Fake(ADV).garb
by (fun; wp).

lemma preGarbDL (ADV <: PrvIndSec.Adv_t): islossless Fake(ADV).preGarbD
by (fun; rnd; skip; smt).

lemma garbDL (ADV <: PrvIndSec.Adv_t): islossless Fake(ADV).garbD.
proof strict.
by fun; call (garbL ADV); wp.
qed.

lemma queryL (ADV <: PrvIndSec.Adv_t): islossless Fake(ADV).query.
proof strict.
fun; sp; if; do !(wp; rnd); skip; smt.
qed.

lemma garbleL (ADV <: PrvIndSec.Adv_t):
  bd_hoare [ Fake(ADV).garble: true ==> true ] = 1%r.
proof strict.
fun.
wp; while true (Fake.n + Fake.q - Fake.g).
  intros=> z; seq 3: (Fake.g < Fake.n + Fake.q /\ Fake.n + Fake.q - Fake.g = z) 1%r 1%r 0%r 0%r=> //.
    by call (garbL ADV); wp.
    by if; do !(wp; call (garbDL ADV)); skip; smt.
    by hoare; call (_: true ==> true)=> //; wp.
wp; while true (Fake.n + Fake.q - Fake.i).
  intros=> z; seq 2: (Fake.i < Fake.n + Fake.q /\ Fake.n + Fake.q - Fake.i = z) 1%r 1%r 0%r 0%r=> //.
    by wp; rnd; skip; smt.
    if.
      seq 3: (Fake.i < Fake.n + Fake.q /\ Fake.n + Fake.q - Fake.i = z) 1%r 1%r 0%r 0%r=> //.
        by wp; rnd; wp; skip; smt.
        by if; wp; skip; smt.
        by hoare; wp; rnd; wp.
      seq 2: (Fake.i < Fake.n + Fake.q /\ Fake.n + Fake.q - Fake.i = z) 1%r 1%r 0%r 0%r=> //.
        by wp; rnd; skip; smt.
        by if; wp; skip; smt.
        by hoare; wp; rnd.
        by hoare; wp; rnd.
wp; while true (Fake.n + Fake.q - Fake.g).
  intros=> z; sp; if.
    do !(wp; rnd); wp; call (preGarbDL ADV); do !call (queryL ADV); skip; smt.
    wp; do !call (preGarbDL ADV); skip; smt.
wp; while true (Fake.n + Fake.q - Fake.i);
  first by intros=> z; wp; skip; smt.
while true (Fake.n + Fake.q - Fake.m - Fake.i);
  first by intros=> z; wp; rnd; skip; smt.
by wp; skip; smt.
qed.

lemma fakePr :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, Fake}) &m,
    islossless ADV.gen_query =>
    islossless ADV.get_challenge =>
    Pr [Fake(ADV).work() @ &m : !res] = 1%r / 2%r.
proof strict.
intros ADV &m h1 h2.
bdhoare_deno (_ : (true) ==> (!res))=> //.
fun.
seq 1 : true (1%r) (1%r/2%r) 0%r 1%r=> //;
  first call (_ : true ==> true);[fun (true)|skip];progress;assumption.
case (PrvIndSec.Scheme.queryValid Fake.query).
  (* VALID *)
  rcondt 1;first skip;progress.
  wp.
  rnd (lambda b, ! (b = challenge) = false).
  call (_ : true ==> true);first fun (true);progress;assumption.
  kill 1!14; first by call (garbleL ADV); wp; rnd; rnd; skip; smt.
  skip;progress;rewrite Dbool.mu_def /=;case (result);delta charfun;simplify;smt.
  (* INVALID *)
  rcondf 1;first skip;progress.
  rnd (lambda b, ! b = false).
  skip;progress.
  rewrite Dbool.mu_def /charfun //.
qed.

equiv fakeEq_garble (ADV <: PrvIndSec.Adv_t {RedAda,DKCS.Dkc,Fake}):
  RedAda(ADV,DKCS.Dkc).garble ~ Fake(ADV).garble:
    ={glob ADV} /\
    RedAda.n{1} = Fake.n{2} /\
    RedAda.q{1} = Fake.q{2} /\
    RedAda.m{1} = Fake.m{2} /\
    RedAda.t{1} = Fake.t{2} /\
    length RedAda.v{1} = RedAda.n{1} + RedAda.q{1} /\
    length RedAda.t{1} = RedAda.n{1} + RedAda.q{1} /\
    RedAda.l{1} = Cst.bound ==>
    ={glob ADV, glob DKCS.Dkc}.
proof strict.
fun.

lemma fakeEq :
  forall (ADV <: PrvIndSec.Adv_t{RedAda, DKCS.Dkc, Fake}),
    equiv [
      PreInit(ADV).f ~
      Fake(ADV).work
      :
      (!vb{1}) /\ (vl{1}=Cst.bound-1) ==> res{1} = res{2}
    ].
proof strict.
  intros ADV.
  fun.
  inline {1} PreInit(ADV).G.work.
  inline {1} DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).A.work.
  inline {1} RedAda(ADV, DKCS.Dkc).work.
  inline {1} RedAda(ADV, DKCS.Dkc).garble.
  inline {1} RedAda(ADV, DKCS.Dkc).query.
  inline {1} RedAda(ADV, DKCS.Dkc).garbD.
  inline {1} RedAda(ADV, DKCS.Dkc).garb.
  inline {1} RedAda(ADV, DKCS.Dkc).preGarbD.
  inline {1} DKCS.Dkc.preInit.
  inline {1} DKCS.Dkc.get_challenge.
  inline {1} DKCS.Dkc.initialize.
  inline {1} DKCS.Dkc.encrypt.
  inline {2} Fake(ADV).work.
  inline {2} Fake(ADV).garble.
  inline {2} Fake(ADV).query.
  inline {2} Fake(ADV).garbD.
  inline {2} Fake(ADV).garb.
  inline {2} Fake(ADV).preGarbD.

  swap{1} 11 -10.

  seq 1 1 : (RedAda.query{1} = Fake.query{2} /\ (!vb{1}) /\ (vl{1}=Cst.bound-1));
    first by call (_ : true ==> res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2});
             [fun true|skip;progress;assumption].
  
  case (PrvIndSec.Scheme.queryValid Fake.query{2});last
    (rcondf {1} 21;first (intros _;wp;rnd;wp;rnd;rnd;wp;skip;smt));
    rcondf {2} 1;[intros &m;skip;smt|];
    (wp;sp;kill{1} 1!18;first admit);
    rnd;skip;progress assumption;smt.

  (*VALID*)
  sp.
  rcondt {1} 19;first (intros _;wp;rnd;wp;rnd;rnd;skip;progress assumption).
  rcondt {2} 1;first (intros &m;skip;by progress).

  swap{1} 9 -8.
  swap{2} 26 -25.

  wp.
  call (_ : (glob ADV){1} = (glob ADV){2}/\ ={glob ADV, cipher} ==> res{1}=res{2});
    first by fun true.
  wp.

(*
       (forall i, i>= 0 => i < Fake.n{2} => RedAda.v{1}.[i] = RedAda.xc{1}.[i]) /\
       (forall i, i>= 0 => i < Fake.n{2} => Fake.v{2}.[i] = Fake.x1{2}.[i]) /\
*)
  while (
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.n{2}+Fake.q{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\

    RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
    true
  ).

    seq 6 6 : (
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.n{2}+Fake.q{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\


    (RedAda.b{1} = Cst.bound-1 /\ evalGate RedAda.gg{1}.[Fake.g{2}]
      ((!RedAda.v{1}.[RedAda.a{1}]), false) = evalGate RedAda.gg{1}.[Fake.g{2}] ((!RedAda.v{1}.[RedAda.a{1}]), true) =>
        RedAda.yy{1}.[Fake.g{2}]=proj Fake.randG{2}.[(Fake.g{2}, true, false)])/\
      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Cst.bound-1 /\
      RedAda.b{1} <= Cst.bound-1 /\
      true
    );first by wp;skip;(progress assumption;smt).
    if;first smt.
      (*IF TRUE*)
      rcondt{1} 4;first (intros _;wp;skip;smt).
      rcondt{1} 13;first (intros _;wp;skip;smt).
      rcondf{1} 19;first (intros _;wp;skip;smt).
      rcondt{1} 22;first (intros _;wp;skip;smt).
      wp;skip;progress assumption;smt.
      (*IF FALSE*)
      rcondf{1} 1;first (intros _;skip;smt).
      cfold{1} 1?1.
      wp;skip;progress assumption;smt.

  wp.

  while (
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.n{2}+Fake.q{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\

    RedAda.i{1} = Fake.i{2} /\
      0 <= Fake.i{2} /\
    true
  );first wp;rnd;wp;rnd;skip;progress assumption;smt.

  wp.
  
  while (
      DKCS.Dkc.ksec{1} = Fake.ksec{2} /\
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\
      (forall g a b, g >= Fake.g{2} => !(mem (tweak g a b) DKCS.Dkc.used{1})) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g < Cst.bound-1 => in_dom (g, x) DKCS.Dkc.kpub{1} = in_dom (g, x) Fake.kpub{2}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\
    (!DKCS.Dkc.b{1}) /\

    RedAda.g{1} = Fake.g{2} /\
    Fake.g{2} >= Fake.n{2} /\
    Fake.g{2} < Fake.n{2}+Fake.q{2} /\
    true
  ).

sp.

  rcondf{1} 1;first intros ?;wp;skip;progress assumption;smt.
  if;first smt.

  cfold{1} 1.
  cfold{1} 1.
  cfold{1} 1.
  cfold{2} 1.
  cfold{2} 1.
  cfold{2} 1.
  cfold{1} 15.
  cfold{1} 15.
  cfold{1} 15.
  cfold{2} 10.
  cfold{2} 10.
  cfold{2} 10.

  rcondf{1} 3;first by intros ?;wp;skip;progress assumption;smt.
  rcondf{1} 6;first by intros ?;rnd;wp;skip;progress assumption;smt.
  rcondt{1} 10;first by intros ?;wp;rnd;wp;skip;progress assumption;smt.
  rcondf{1} 17;first by intros ?;wp;(kill 12!3;first admit);wp;rnd;wp;rnd;wp;rnd;wp;skip;progress assumption.
  rcondf{1} 19;first by intros ?;(kill 1!18;first admit);skip;progress assumption;smt.
  rcondf{1} 23;first by intros ?;(kill 1!22;first admit);skip;progress assumption;smt.
  rcondt{1} 24;first by intros ?;(kill 1!23;first admit);wp;skip;progress assumption;smt.
  rcondf{1} 28;first by intros ?;(kill 1!27;first admit);wp;skip;progress assumption;smt.
  rcondt{1} 31;first by intros ?;(kill 1!30;first admit);wp;skip;progress assumption;smt.
  rcondt{1} 35;first by intros ?;wp;rnd;wp;(kill 12!3;first admit);wp;rnd;wp;rnd;wp;rnd;wp;skip;progress assumption;smt.
  rcondf{1} 42;first by intros ?;wp;(kill 35!5;first admit);wp;rnd;wp;rnd;wp;conseq (_: true ==> true);(kill 1!14;first admit).
  rcondf{1} 44;first by intros ?;(kill 1!43;first admit);skip;by progress assumption.
  rcondf{1} 48;first by intros ?;(kill 1!47;first admit);skip;progress assumption;smt.
  rcondf{1} 49;first by intros ?;(kill 1!48;first admit);skip;by progress assumption.
  rcondf{1} 50;first by intros ?;(kill 1!49;first admit);skip;progress assumption;smt.
  rcondf{1} 50;first by intros ?;(kill 1!49;first admit);skip;progress assumption;smt.
  rcondt{1} 53;first by intros ?;wp;conseq (_: true ==> true);(kill 1!40;first admit).
  rcondt{1} 16;first by intros ?;(kill 12!4;first admit);wp;rnd;wp;rnd;wp;skip;progress assumption;smt.
  rcondt{1} 41;first intros ?;(kill 37!4;first admit);wp;rnd;wp;rnd;wp;rnd;wp;rnd;wp;rnd;wp;rnd;wp;skip;progress assumption;smt.

(*
  rcondt{1} 12;first intros ?;sp;(kill 1;first rnd;skip;smt);sp;
  case (! in_dom input1 DKCS.Dkc.kpub);[
  (rcondt 4;first wp;skip;smt);
  wp;rnd;wp;skip;progress assumption;
  cut := H11 Fake.g{m} (Fake.t{m}.[Fake.g{m}] ^^
   (RedAda.v{hr}.[Fake.g{m}] ^^
    evalGate RedAda.gg{hr}.[Fake.g{m}]
      (RedAda.v{hr}.[Fake.aa{m}.[Fake.g{m}]] ^^ false,
       RedAda.v{hr}.[Fake.bb{m}.[Fake.g{m}]] ^^ true))) _;smt|
  (rcondf 4;first wp;skip;smt);wp;skip;progress assumption;smt].

  rcondt{1} 35;first
intros ?;sp;(kill 1;first rnd;skip;smt);sp;
  (seq 26 : (! in_dom j2 DKCS.Dkc.kpub /\ j2 <> i2);
    last if;wp;(try rnd);skip;progress assumption;smt);
  (do !(wp;rnd));
  case (! in_dom input1 DKCS.Dkc.kpub);
[
  (rcondt 4;first wp;skip;smt);
  wp;rnd;wp;skip;(progress assumption;last smt);
  rewrite ! in_dom_set;(cut := H12 (Fake.g{m} + Fake.n{m} + Fake.q{m}) ra20 _;first smt);rewrite - !rw_nor;intros ?;split;smt|
  (rcondf 4;first wp;skip;smt);wp;skip;progress assumption;smt].
*)
  kill{1} 5;first rnd cpTrue;skip;smt.

  cfold{1} 49.
  cfold{1} 49.
  cfold{1} 49.

  alias{1} 53 with tok_g_false_end;swap{1} 53 -52.
  alias{1} 51 with tok_g_true_end;swap{1} 51 -50.
  alias{1} 51 with randG_g_true_false;swap{1} 51 -50.
  alias{1} 42 with r_gnq_randbit;swap{1} 42 -41.
  alias{1} 41 with kpub_gnq_randbit;swap{1} 41 -40.
  alias{1} 40 with kpub_a_tatrue;swap{1} 40 -39.
  alias{1} 35 with randbit;swap{1} 35 -34.
  alias{1} 21 with r_g_tggamma1;swap{1} 21 -20.
  alias{1} 20 with kpub_g_tggamma1;swap{1} 20 -19.
  alias{1} 19 with kpub_a_tafalse;swap{1} 19 -18.

  alias{2} 24 with tok_g_false_end;swap{2} 24 -23.
  alias{2} 23 with tok_g_true_end;swap{2} 23 -22.
  alias{2} 23 with randG_g_true_false;swap{2} 23 -22.
  alias{2} 17 with pp_g_tatrue_tbtrue;swap{2} 17 -16.
  alias{2} 16 with kpub_a_tatrue;swap{2} 16 -15.
  alias{2} 10 with pp_g_tafalse_tbtrue;swap{2} 10 -9.
  alias{2} 9 with kpub_a_tafalse;swap{2} 9 -8.

  wp.

  swap{1} 5 2.
  swap{2} 3 1.
  swap{1} 1 5.
  swap{2} 1 2.

  rnd.
  rnd.
  rnd.
  rnd.
  rnd.

  rnd{1}.
  rnd{1}.
  rnd{1}.
  rnd{1}.
  rnd{1}.

  rnd{2}.
  rnd{2}.

  skip.

simplify.


do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).

split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt .
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.
do ((do ? (intros [_H1 _H2];generalize _H1 _H2));intros ?).
split;first smt.

do (intros ?).
split;first smt.
split;first smt.

  progress.
smt.
smt.
smt.

  eager if.

  sp.

  seq 3 0 : (
  mem t2{1} DKCS.Dkc.used{1} /\
  out1{1} = DKCS.bad /\
  (i1{1}, j1{1}, pos5{1}, t2{1}) = q1{1} /\
  input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
  ttt{2} =
  tweak Fake.g{2} (Fake.t{2}.[Fake.a{2}] ^^ false)
    (Fake.t{2}.[Fake.b{2}] ^^ true) /\
  q1{1} = (input1{1}, output1{1}, pos1{1}, ttt1{1}) /\
  output1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\
  input1{1} = (RedAda.a{1}, RedAda.t{1}.[RedAda.a{1}] ^^ false) /\
  pos1{1} = false /\
  gamma1{1} =
  RedAda.v{1}.[RedAda.g{1}] ^^
  evalGate RedAda.gg{1}.[RedAda.g{1}]
    (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
  ttt1{1} =
  tweak RedAda.g{1} (RedAda.t{1}.[RedAda.a{1}] ^^ false)
    (RedAda.t{1}.[RedAda.b{1}] ^^ true) /\
  Fake.b{2} = Fake.bb{2}.[Fake.g{2}] /\
   Fake.a{2} = Fake.aa{2}.[Fake.g{2}] /\
   RedAda.b{1} = RedAda.bb{1}.[RedAda.g{1}] /\
   RedAda.a{1} = RedAda.aa{1}.[RedAda.g{1}] /\

      DKCS.Dkc.ksec{1} = Fake.ksec{2} /\
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g < Cst.bound-1 => in_dom (g, x) DKCS.Dkc.kpub{1} = in_dom (g, x) Fake.kpub{2}) /\
    (!DKCS.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\



      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Fake.g{2} /\
      RedAda.b{1} < Fake.g{2} /\
      RedAda.a{1} < Cst.bound-1 /\
      RedAda.b{1} <= Cst.bound-1 /\
      i1{1} = input{2} /\
      input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKCS.Dkc.used{1})) /\

      gamma1{1} = RedAda.v{1}.[RedAda.g{1}] ^^ evalGate RedAda.gg{1}.[RedAda.g{1}] (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
      j1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\

      true
    );first wp;skip;progress assumption.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.

  seq 1 1 : (
  mem t2{1} DKCS.Dkc.used{1} /\
  out1{1} = DKCS.bad /\
  (i1{1}, j1{1}, pos5{1}, t2{1}) = q1{1} /\
      DKCS.Dkc.ksec{1} = Fake.ksec{2} /\
  input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
  ttt{2} =
  tweak Fake.g{2} (Fake.t{2}.[Fake.a{2}] ^^ false)
    (Fake.t{2}.[Fake.b{2}] ^^ true) /\
  q1{1} = (input1{1}, output1{1}, pos1{1}, ttt1{1}) /\
  output1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\
  input1{1} = (RedAda.a{1}, RedAda.t{1}.[RedAda.a{1}] ^^ false) /\
  pos1{1} = false /\
  gamma1{1} =
  RedAda.v{1}.[RedAda.g{1}] ^^
  evalGate RedAda.gg{1}.[RedAda.g{1}]
    (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
  ttt1{1} =
  tweak RedAda.g{1} (RedAda.t{1}.[RedAda.a{1}] ^^ false)
    (RedAda.t{1}.[RedAda.b{1}] ^^ true) /\
  Fake.b{2} = Fake.bb{2}.[Fake.g{2}] /\
   Fake.a{2} = Fake.aa{2}.[Fake.g{2}] /\
   RedAda.b{1} = RedAda.bb{1}.[RedAda.g{1}] /\
   RedAda.a{1} = RedAda.aa{1}.[RedAda.g{1}] /\


      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g < Cst.bound-1 => in_dom (g, x) DKCS.Dkc.kpub{1} = in_dom (g, x) Fake.kpub{2}) /\
    (!DKCS.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\



      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Fake.g{2} /\
      RedAda.b{1} < Fake.g{2} /\
      RedAda.a{1} < Cst.bound-1 /\
      RedAda.b{1} <= Cst.bound-1 /\
      i1{1} = input{2} /\
      input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKCS.Dkc.used{1})) /\

      gamma1{1} = RedAda.v{1}.[RedAda.g{1}] ^^ evalGate RedAda.gg{1}.[RedAda.g{1}] (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
      j1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\

      true
    );first if;[ |wp;rnd;skip|skip];progress assumption;rewrite ? in_dom_set;smt.

    alias{1} 37 with mytok1.
    swap{1} 37 -35.
    alias{2} 17 with mytok1.
    swap{2} 17 -16.


    alias{1} 41 with mytok2.
    swap{1} 41 -38.
    alias{2} 20 with mytok2.
    swap{2} 20 -18.

    rcondt{1} 1;first intros ?;skip;progress;smt.

    rcondt{1} 26;first intros ?;
seq 24 : ((! in_dom j2 DKCS.Dkc.kpub) /\ (i2 = (RedAda.a, RedAda.t.[RedAda.a] ^^ true))/\(j2 = (RedAda.g + RedAda.n + RedAda.q, ra2))/\RedAda.g + RedAda.n + RedAda.q<>RedAda.a);
[ |if];do ? (wp;rnd);skip;progress;rewrite ? in_dom_set;smt.

  alias{1} 26 with leftpart.
  swap{1} 26 -6.

  seq 25 9 : (
  input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
  ttt{2} =
  tweak Fake.g{2} (Fake.t{2}.[Fake.a{2}] ^^ false)
    (Fake.t{2}.[Fake.b{2}] ^^ true) /\
  q1{1} = (input1{1}, output1{1}, pos1{1}, ttt1{1}) /\
  output1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\
  input1{1} = (RedAda.a{1}, RedAda.t{1}.[RedAda.a{1}] ^^ false) /\
  pos1{1} = false /\
  gamma1{1} =
  RedAda.v{1}.[RedAda.g{1}] ^^
  evalGate RedAda.gg{1}.[RedAda.g{1}]
    (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
  ttt1{1} =
  tweak RedAda.g{1} (RedAda.t{1}.[RedAda.a{1}] ^^ false)
    (RedAda.t{1}.[RedAda.b{1}] ^^ true) /\
  Fake.b{2} = Fake.bb{2}.[Fake.g{2}] /\
   Fake.a{2} = Fake.aa{2}.[Fake.g{2}] /\
   RedAda.b{1} = RedAda.bb{1}.[RedAda.g{1}] /\
   RedAda.a{1} = RedAda.aa{1}.[RedAda.g{1}] /\


      DKCS.Dkc.ksec{1} = Fake.ksec{2} /\ 
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g < Cst.bound-1 => in_dom (g, x) DKCS.Dkc.kpub{1} = in_dom (g, x) Fake.kpub{2}) /\
    (!DKCS.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\



      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Fake.g{2} /\
      RedAda.b{1} < Fake.g{2} /\
      RedAda.a{1} < Cst.bound-1 /\
      RedAda.b{1} <= Cst.bound-1 /\
      i2{1} = input0{2} /\ 
      input0{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ true) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKCS.Dkc.used{1})) /\

      gamma1{1} = RedAda.v{1}.[RedAda.g{1}] ^^ evalGate RedAda.gg{1}.[RedAda.g{1}] (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
      j1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\


      mytok1{1} = mytok1{2} /\
      mytok2{1} = mytok2{2} /\


      true
    );first last.

  seq 1 1 : (
  input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
  ttt{2} =
  tweak Fake.g{2} (Fake.t{2}.[Fake.a{2}] ^^ false)
    (Fake.t{2}.[Fake.b{2}] ^^ true) /\
  q1{1} = (input1{1}, output1{1}, pos1{1}, ttt1{1}) /\
  output1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\
  input1{1} = (RedAda.a{1}, RedAda.t{1}.[RedAda.a{1}] ^^ false) /\
  pos1{1} = false /\
  gamma1{1} =
  RedAda.v{1}.[RedAda.g{1}] ^^
  evalGate RedAda.gg{1}.[RedAda.g{1}]
    (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
  ttt1{1} =
  tweak RedAda.g{1} (RedAda.t{1}.[RedAda.a{1}] ^^ false)
    (RedAda.t{1}.[RedAda.b{1}] ^^ true) /\
  Fake.b{2} = Fake.bb{2}.[Fake.g{2}] /\
   Fake.a{2} = Fake.aa{2}.[Fake.g{2}] /\
   RedAda.b{1} = RedAda.bb{1}.[RedAda.g{1}] /\
   RedAda.a{1} = RedAda.aa{1}.[RedAda.g{1}] /\

      DKCS.Dkc.ksec{1} = Fake.ksec{2} /\
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = Cst.bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.r{1}) /\
      (forall g (x:bool), g < Cst.bound-1 => in_dom (g, x) DKCS.Dkc.kpub{1} = in_dom (g, x) Fake.kpub{2}) /\
    (!DKCS.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKCS.Dkc.kpub{1}) /\



      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Fake.g{2} /\
      RedAda.b{1} < Fake.g{2} /\
      RedAda.a{1} < Cst.bound-1 /\
      RedAda.b{1} <= Cst.bound-1 /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKCS.Dkc.used{1})) /\

      gamma1{1} = RedAda.v{1}.[RedAda.g{1}] ^^ evalGate RedAda.gg{1}.[RedAda.g{1}] (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
      j1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\

      mytok1{1} = mytok1{2} /\
      mytok2{1} = mytok2{2} /\

      true
    );first if;[ |wp;rnd;skip|skip];progress assumption;smt.
   wp.
    cfold{1} 12.
    cfold{1} 12.
    cfold{1} 12.
    cfold{2} 6.
    cfold{2} 6.
   wp.
(*BEGIN WORKING*)

rnd.
wp.
rnd.
wp.
skip.
progress assumption.
smt.
smt.
congr => //.
congr => //.
congr => //.
smt.
congr => //.
admit.
admit.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.

congr=> //.
congr=> //.
congr=> //.
rewrite (Map.get_set DKCS.Dkc.r{1}) ? proj_some=> //.
admit.
congr=> //.

rewrite ! set_set_tok;first 4 smt.
smt.
simplify.
smt.
      case (evalGate RedAda.gg{1}.[Fake.g{2}]
      ((!RedAda.v{1}.[RedAda.aa{1}.[Fake.g{2}]]), false) = evalGate RedAda.gg{1}.[Fake.g{2}] ((!RedAda.v{1}.[RedAda.aa{1}.[Fake.g{2}]]), true)).

    wp.

    swap{1} 35 -10.
    swap{2} 16 -5.
    wp;rnd.

  seq 24 10 : (
      Fake.ev{2} = Garble.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      RedAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\



      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Fake.g{2} /\
      RedAda.b{1} < Fake.g{2} /\
      RedAda.a{1} < bound-1 /\
      RedAda.b{1} <= bound-1 /\
      i1{1} = input{2} /\
      input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      gamma1{1} = RedAda.v{1}.[RedAda.g{1}] ^^ evalGate RedAda.gg{1}.[RedAda.g{1}] (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true) /\
      j1{1} = (RedAda.g{1}, RedAda.t{1}.[RedAda.g{1}] ^^ gamma1{1}) /\
      getTok RedAda.xx{1} RedAda.g{1} false = void /\
      j2{1} = (RedAda.g{1} + RedAda.n{1} + RedAda.q{1}, ra2{1}) /\

      true
    );first last.
      rcondt{1} 2;first intros ?;rnd;skip;progress;smt.

      case (evalGate RedAda.gg{1}.[Fake.g{2}]
      ((!RedAda.v{1}.[RedAda.aa{1}.[Fake.g{2}]]), false) = evalGate RedAda.gg{1}.[Fake.g{2}] ((!RedAda.v{1}.[RedAda.aa{1}.[Fake.g{2}]]), true)).
      
      wp.
      rnd.
      rnd{1}.
      skip.
      

 progress;try assumption.
      delta setTok;simplify;rewrite ! set_length;trivial.
rewrite !set_set_tok;first 4 smt.
   generalize H33.
   generalize H34.
rewrite ! set_get_tok;first 6 smt.
simplify.
intros h1 h2.
congr.
admit.
trivial.
trivial.
congr.
split.
congr.
congr.
trivial.
congr.
split.
trivial.
congr.
admit.
smt.
congr.


delta PartialGet.__get.
simplify.
smt.
    if;[ |wp;rnd;skip|skip];progress assumption;rewrite ? in_dom_set;smt.




wp;skip;progress assumption;smt.

  if;first progress assumption;smt.


  rcondt{1} 1;first intros ?;skip;progress assumption;smt.

  rcondt{1} 24;first intros ?;seq 22 : (!(in_dom j2{hr} DKC.Dkc.kpub{hr})/\i2 <> j2);[wp;rnd;wp;rnd;wp;rnd;skip|if;[wp;rnd;skip|skip]];progress assumption;rewrite ? in_dom_setNE;smt.


progress assumption;smt.
progress assumption;smt.

(* PROBLEME IF
JE VEUX CFOLD !!!!!!!!!!
*)


  rcondt{1} 1;first intros ?;skip;progress assumption;smt.

  case (RedAda.t{1}.[RedAda.g{1}] ^^ RedAda.v{1}.[RedAda.g{1}] ^^ evalGate RedAda.gg{1}.[RedAda.g{1}] (RedAda.v{1}.[RedAda.a{1}] ^^ false, RedAda.v{1}.[RedAda.b{1}] ^^ true)).

  

  seq 33 12 : (
      Fake.ev{2} = Garble.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      RedAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => RedAda.bb{1}.[g] = bound-1 /\ evalGate RedAda.gg{1}.[g]
      ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), false) = evalGate RedAda.gg{1}.[g] ((!RedAda.v{1}.[RedAda.aa{1}.[g]]), true) =>
        RedAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\



      RedAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      RedAda.a{1} = Fake.a{2} /\
      RedAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      RedAda.a{1} < Fake.g{2} /\
      RedAda.b{1} < Fake.g{2} /\
      RedAda.a{1} < bound-1 /\
      RedAda.b{1} <= bound-1 /\
      (forall g a b, g >= Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      !(in_dom input{2} DKC.Dkc.kpub{2}) /\


      true
    );first last.
    admit.



  if.
  progress assumption.
smt.

wp.

  wp.



if.

skip;progress assumption.
(kill 8;first admit);wp;skip;progress assumption;smt.
  wp.

END WORKING
*)
admit.
admit.
admit.
  wp.
  while (
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      getN RedAda.fc{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      getM RedAda.fc{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      getQ RedAda.fc{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.q{2} >= Fake.m{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\

    RedAda.i{1} = Fake.i{2} /\
      Fake.i{2} >= Fake.n{2} + Fake.q{2} - Fake.m{2} /\
    true
  );first (wp;skip;progress assumption;first (rewrite ! set_length;try assumption));smt.

  while (
      Fake.ev{2} = GC.GarbleCircuit.eval RedAda.fc{1} RedAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length RedAda.xx{1} = RedAda.n{1}+RedAda.q{1} /\
      length RedAda.t{1} = RedAda.n{1}+RedAda.q{1} /\
      RedAda.xx{1} = Fake.xx{2}/\
      RedAda.t{1} = Fake.t{2}/\
      RedAda.n{1} = Fake.n{2}/\
      getN RedAda.fc{1} = Fake.n{2}/\
      RedAda.m{1} = Fake.m{2}/\
      getM RedAda.fc{1} = Fake.m{2}/\
      RedAda.q{1} = Fake.q{2}/\
      getQ RedAda.fc{1} = Fake.q{2}/\
      RedAda.aa{1} = Fake.aa{2}/\
      RedAda.bb{1} = Fake.bb{2}/\
      RedAda.randG{1} = Fake.randG{2}/\
      RedAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = Cst.bound /\
      RedAda.l{1} = Cst.bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < Cst.bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\

    RedAda.i{1} = Fake.i{2} /\
      Fake.i{2} >= 0 /\
    true
  );first (
  wp;
  rnd;
  wp;skip;progress assumption);smt.

wp.
swap 1 1.
wp.
rnd.
rnd.
rnd.
skip.

  cut lem : (forall (x:int), x <= x);first smt.
  delta PrvIndSec.Scheme.queryValid.
  delta PrvInd_Circuit.Scheme.queryValid.
  delta phi.
  delta PrvInd_Circuit.Garble.functCorrect.
  delta functCorrect.
  simplify.
  rewrite ! valid_wireinput.
  delta fst snd getN getM getQ.
  intros &1 &2.
  elimT tuple2_ind Fake.query{2}.
  intros query1 query2 queryVal.

  elimT tuple2_ind query1.
  intros f1 x1 query1val.
  elimT tuple6_ind f1.
  intros n1 m1 q1 aa1 bb1 gg1 f1val.

  elimT tuple2_ind query2.
  intros f2 x2 query2val.
  elimT tuple6_ind f2.
  intros n2 m2 q2 aa2 bb2 gg2 f2val.

  intros h.

    cut rew : (length x1 = length x2);first generalize h;simplify delta;smt.
    cut lem0 : (0 <= 0);first smt.
    cut lem1 : (0 >= 0);first smt.
    cut lem2 : (length x2 >= length x2);first smt.
    cut lem3 : (length x2 >= 1);first generalize h;simplify delta;smt.
    cut lem4 : (0 <= length x2 + q2);first smt.

  generalize h.

  generalize Cst.bound.
  intros bound.

  subst;simplify PrvInd_Circuit.Garble.inputCorrect inputCorrect.

  rewrite rew.

  delta.

  progress assumption;rewrite ? H64;smt.
save.
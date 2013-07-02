require import Bitstring.
require import List.
require import Map.
import PartialGet.
require import Set.
require import Pair.
require import Real.
require import Int.
require import Bool.
require import Array.
require import Distr.

require import CloneDkc.
require import GarbleTools.
require import Garble.
require import AdvGarbleAda.

module Fake(A:Garble.Adv) = {

  var f1 : Garble.funct
  var x1 : Garble.input
  var ev : Garble.output
  var good : bool
  var tau : bool
  var queries : DKC.query array
  var ans : DKC.answer array
  var answer : Garble.functG*Garble.inputG*Garble.keyOutput
  var query : Garble.query

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

    ttt = tweak g (t.[a]^^alpha) (t.[b]^^bet);
    input = (a, (t.[a]^^alpha));

    (*DKC encrypt*)
        if (! (in_dom input DKC.Dkc.kpub)) {DKC.Dkc.kpub.[input] = $DKC.genRandKeyLast; DKC.Dkc.kpub.[input] = DKC.addLast DKC.Dkc.kpub.[input] (snd input);}
        tok = $DKC.genRandKey;
        ki = kpub.[input];
        zz = DKC.encode ttt ki ksec tok;
    (*End DKC encrypt*)
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) zz;
    xx = setTok xx g alpha ki;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) (DKC.encode
      (tweak g (t.[a]^^alpha) (t.[b]^^bet))
      (getTok xx a alpha)
      (getTok xx b bet)
      yy);
  }

  fun garbD(alpha:bool, bet:bool) : token = {
    var yy : token;
    yy = randG.[(g,alpha,bet)];
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


    t.[bound-1] = !tau;

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      if (b = bound - 1) {
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
      if (getTok xx i true = void /\ i <> bound - 1) {
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
      if (b <> bound - 1) {
        tok = garbD(false, true);
        tok = garbD(true, true);
        tok = garbD(true, false);
      } else {
        tok = garbD(true, false);
      }
      g = g + 1;
    }
    answer = ((getN f1, getM f1, getQ f1, getA f1, getB f1, pp), encrypt (Array.sub xx 0 (getN f1)) (Array.init (getN f1) false),tt);
  }

  fun work() : bool = {
    var challenge : bool;
    var c : bool;
    var ret : bool;
    var gg : bool g2v;

    query = A.gen_query();
  
    if (Garble.queryValid query)
    {
      tau = $Dbool.dbool;
      ksec = $DKC.genRandKeyLast;
      ksec = DKC.addLast ksec tau;
      kpub = Map.empty;
      r = Map.empty;

      (f1, x1) = fst query;
      (n, m, q, aa, bb, gg) = f1;
      ev = Garble.eval f1 x1;
      queries = Array.empty;
      t = Array.init (n+q) false;
      xx = Array.init (n+q) (void, void);
      pp = Array.init (n+q) (void, void, void, void);
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

lemma fakePr :
  forall (ADV <: Garble.Adv{AdvAda, DKC.Dkc, Fake}) &m,
    islossless ADV.gen_query =>
    islossless ADV.get_challenge =>
    Pr [Fake(ADV).work() @ &m : res] = 1%r / 2%r.
intros ADV &m h1 h2.
bdhoare_deno (_ : (true) ==> (res));last 2 by progress.
fun.
seq 1 : (true).
call (_ : true ==> true);[fun (true)|skip];progress;assumption.
case (queryValid Fake.query).
  (* VALID *)
  rcondt 1;first skip;progress.
  wp.
  rnd (1%r/2%r) (lambda b, (b = challenge) = false).
  call (_ : true ==> true);first fun (true);progress;assumption.
  kill 1!14;first admit. (*TERMINATE*)
  skip;progress;rewrite Dbool.mu_def;case (result);delta charfun;simplify;smt.
  (* INVALID *)
  rcondf 1;first skip;progress.
  rnd (1%r/2%r) (lambda b, b = false).
  skip;progress;smt "Z3".
save.

lemma fakeEq :
  forall (ADV <: Garble.Adv{AdvAda, DKC.Dkc, Fake}),
    equiv [
      GameAda(DKC.Dkc, ADV).work ~
      Fake(ADV).work
      : (glob ADV){1} = (glob ADV){2} /\
      (!DKC.Dkc.b{1}) /\ (AdvAda.l{1}=bound-1) ==> res{1} = res{2}
    ].
proof strict.
  intros ADV.
  fun.
  inline {1} GameAda(DKC.Dkc, ADV).A.work.
  inline {1} AdvAda(ADV, DKC.Dkc).work.
  inline {1} AdvAda(ADV, DKC.Dkc).garble.
  inline {1} AdvAda(ADV, DKC.Dkc).query.
  inline {1} AdvAda(ADV, DKC.Dkc).garbD.
  inline {1} AdvAda(ADV, DKC.Dkc).garb.
  inline {1} AdvAda(ADV, DKC.Dkc).preGarbD.
  inline {1} DKC.Dkc.preInit.
  inline {1} DKC.Dkc.get_challenge.
  inline {1} DKC.Dkc.initialize.
  inline {1} DKC.Dkc.encrypt.
  inline {2} Fake(ADV).work.
  inline {2} Fake(ADV).garble.
  inline {2} Fake(ADV).query.
  inline {2} Fake(ADV).garbD.
  inline {2} Fake(ADV).garb.
  inline {2} Fake(ADV).preGarbD.

  swap{1} 9 -8.

  seq 1 1 : ((glob ADV){1} = (glob ADV){2}/\AdvAda.query{1} = Fake.query{2} /\ (!DKC.Dkc.b{1}) /\ (AdvAda.l{1}=bound-1)).
    call (_ : (glob ADV){1} = (glob ADV){2} ==> res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2});first (fun true;by progress).
  skip;progress;assumption.
  
  case (Garble.queryValid Fake.query{2}).

  (*VALID*)
  rcondt {1} 19;first (intros _;wp;rnd;wp;rnd;rnd;skip;progress assumption).
  rcondt {2} 1;first (intros &m;skip;by progress).

  swap{1} 9 -8.
  swap{2} 26 -25.

  wp.
  call (_ : (glob ADV){1} = (glob ADV){2}/\answer{1}=answer{2} ==> res{1}=res{2});first (fun true;by progress).
  wp.

(*
       (forall i, i>= 0 => i < Fake.n{2} => AdvAda.v{1}.[i] = AdvAda.xc{1}.[i]) /\
       (forall i, i>= 0 => i < Fake.n{2} => Fake.v{2}.[i] = Fake.x1{2}.[i]) /\
*)

  while (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.n{2}+Fake.q{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\

    AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
    true
  ).

    seq 6 6 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.n{2}+Fake.q{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\


    (AdvAda.b{1} = bound-1 /\ evalGate AdvAda.gg{1}.[Fake.g{2}]
      ((!AdvAda.v{1}.[AdvAda.a{1}]), false) = evalGate AdvAda.gg{1}.[Fake.g{2}] ((!AdvAda.v{1}.[AdvAda.a{1}]), true) =>
        AdvAda.yy{1}.[Fake.g{2}]=Fake.randG{2}.[(Fake.g{2}, true, false)])/\
      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      true
    );first wp;skip;(progress assumption;first apply H6);smt.
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
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.n{2}+Fake.q{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\

    AdvAda.i{1} = Fake.i{2} /\
      0 <= Fake.i{2} /\
    true
  );first wp;rnd;wp;rnd;skip;progress assumption;smt.

  wp.

  while (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g a b, g >= Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
    (!DKC.Dkc.b{1}) /\

    AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
    true
  ).

    seq 2 2 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
    (!DKC.Dkc.b{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      (forall g a b, g >= Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\
      true
    );first wp;skip;progress assumption;smt.
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
  cfold{2} 9.
  cfold{2} 9.
  cfold{2} 9.

  rcondf{1} 3;first intros ?;wp;skip;progress assumption;smt.
  rcondf{1} 6;first intros ?;rnd;wp;skip;progress assumption;smt.
  rcondt{1} 10;first intros ?;wp;rnd;wp;skip;progress assumption;smt.
  rcondf{1} 14;first intros ?;(kill 11!3;first admit);wp;rnd;wp;skip;progress assumption;smt.
  rcondf{1} 16;first intros ?;(kill 1!15;first admit);skip;progress assumption;smt.
  rcondf{1} 20;first intros ?;(kill 1!19;first admit);skip;progress assumption;smt.
  rcondt{1} 21;first intros ?;(kill 1!20;first admit);wp;skip;progress assumption;smt.
  rcondf{1} 25;first intros ?;(kill 1!24;first admit);wp;skip;progress assumption;smt.
  rcondt{1} 28;first intros ?;(kill 1!27;first admit);wp;skip;progress assumption;smt.
  rcondt{1} 32;first intros ?;wp;rnd;wp;(kill 11!3;first admit);wp;rnd;wp;skip;(progress assumption;
    first rewrite Set.add_mem;rewrite tweak_inj2);smt.
  rcondf{1} 36;first intros ?;wp;(kill 31!5;first admit);wp;rnd;wp;(kill 1!13;first admit);skip;by progress assumption.
  rcondf{1} 38;first intros ?;(kill 1!37;first admit);skip;by progress assumption.
  rcondf{1} 42;first intros ?;(kill 1!41;first admit);skip;progress assumption;smt.
  rcondf{1} 43;first intros ?;(kill 1!42;first admit);skip;by progress assumption.
  rcondf{1} 44;first intros ?;(kill 1!43;first admit);skip;progress assumption;smt.
  rcondf{1} 44;first intros ?;(kill 1!43;first admit);skip;progress assumption;smt.
  rcondt{1} 47;first intros ?;wp;(kill 1!35;first admit);skip;progress assumption;smt.
  rcondt{1} 13;first intros ?;(kill 9!4;first admit);wp;rnd;wp;skip;progress assumption;smt.
  rcondt{1} 35;first intros ?;(kill 31!4;first admit);wp;rnd;wp;rnd;(kill 11!2;first admit); wp;rnd;wp;skip;progress assumption;smt.

  kill{1} 5;first rnd 1%r cpTrue;skip;smt.

  seq 9 2 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      i1{1} = input{2} /\
      input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      gamma1{1} = AdvAda.v{1}.[AdvAda.g{1}] ^^ evalGate AdvAda.gg{1}.[AdvAda.g{1}] (AdvAda.v{1}.[AdvAda.a{1}] ^^ false, AdvAda.v{1}.[AdvAda.b{1}] ^^ true) /\
      j1{1} = (AdvAda.g{1}, AdvAda.t{1}.[AdvAda.g{1}] ^^ gamma1{1}) /\

      true
    );first wp;skip;progress assumption;smt.


  seq 1 1 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      i1{1} = input{2} /\
      input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      gamma1{1} = AdvAda.v{1}.[AdvAda.g{1}] ^^ evalGate AdvAda.gg{1}.[AdvAda.g{1}] (AdvAda.v{1}.[AdvAda.a{1}] ^^ false, AdvAda.v{1}.[AdvAda.b{1}] ^^ true) /\
      j1{1} = (AdvAda.g{1}, AdvAda.t{1}.[AdvAda.g{1}] ^^ gamma1{1}) /\

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
seq 24 : ((! in_dom j2 DKC.Dkc.kpub) /\ (i2 = (AdvAda.a, AdvAda.t.[AdvAda.a] ^^ true))/\(j2 = (AdvAda.g + AdvAda.n + AdvAda.q, ra2))/\AdvAda.g + AdvAda.n + AdvAda.q<>AdvAda.a);
[ |if];do ? (wp;rnd);skip;progress;rewrite ? in_dom_set;smt.

  alias{1} 26 with leftpart.
  swap{1} 26 -6.

  seq 25 9 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      i2{1} = input0{2} /\ 
      input0{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ true) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      gamma1{1} = AdvAda.v{1}.[AdvAda.g{1}] ^^ evalGate AdvAda.gg{1}.[AdvAda.g{1}] (AdvAda.v{1}.[AdvAda.a{1}] ^^ false, AdvAda.v{1}.[AdvAda.b{1}] ^^ true) /\
      j1{1} = (AdvAda.g{1}, AdvAda.t{1}.[AdvAda.g{1}] ^^ gamma1{1}) /\

      true
    );first last.

  seq 1 1 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      gamma1{1} = AdvAda.v{1}.[AdvAda.g{1}] ^^ evalGate AdvAda.gg{1}.[AdvAda.g{1}] (AdvAda.v{1}.[AdvAda.a{1}] ^^ false, AdvAda.v{1}.[AdvAda.b{1}] ^^ true) /\
      j1{1} = (AdvAda.g{1}, AdvAda.t{1}.[AdvAda.g{1}] ^^ gamma1{1}) /\

      true
    );first if;[ |wp;rnd;skip|skip];progress assumption;rewrite ? in_dom_set;smt.


   wp.
    cfold{1} 12.
    cfold{1} 12.
    cfold{1} 12.
    cfold{2} 6.
    cfold{2} 6.
   wp.

      case (evalGate AdvAda.gg{1}.[Fake.g{2}]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[Fake.g{2}]]), false) = evalGate AdvAda.gg{1}.[Fake.g{2}] ((!AdvAda.v{1}.[AdvAda.aa{1}.[Fake.g{2}]]), true)).

    wp.

    swap{1} 35 -10.
    swap{2} 16 -5.
    wp;rnd.

  seq 24 10 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.kpub{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
      i1{1} = input{2} /\
      input{2} = (Fake.a{2}, Fake.t{2}.[Fake.a{2}] ^^ false) /\
      (forall g a b, g > Fake.g{2} => !(mem (tweak g a b) DKC.Dkc.used{1})) /\

      gamma1{1} = AdvAda.v{1}.[AdvAda.g{1}] ^^ evalGate AdvAda.gg{1}.[AdvAda.g{1}] (AdvAda.v{1}.[AdvAda.a{1}] ^^ false, AdvAda.v{1}.[AdvAda.b{1}] ^^ true) /\
      j1{1} = (AdvAda.g{1}, AdvAda.t{1}.[AdvAda.g{1}] ^^ gamma1{1}) /\
      getTok AdvAda.xx{1} AdvAda.g{1} false = void /\
      j2{1} = (AdvAda.g{1} + AdvAda.n{1} + AdvAda.q{1}, ra2{1}) /\

      true
    );first last.
      rcondt{1} 2;first intros ?;rnd;skip;progress;smt.

      case (evalGate AdvAda.gg{1}.[Fake.g{2}]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[Fake.g{2}]]), false) = evalGate AdvAda.gg{1}.[Fake.g{2}] ((!AdvAda.v{1}.[AdvAda.aa{1}.[Fake.g{2}]]), true)).
      
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

  case (AdvAda.t{1}.[AdvAda.g{1}] ^^ AdvAda.v{1}.[AdvAda.g{1}] ^^ evalGate AdvAda.gg{1}.[AdvAda.g{1}] (AdvAda.v{1}.[AdvAda.a{1}] ^^ false, AdvAda.v{1}.[AdvAda.b{1}] ^^ true)).

  

  seq 33 12 : (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, g >= Fake.n{2} => g < Fake.g{2} => AdvAda.bb{1}.[g] = bound-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true) =>
        AdvAda.yy{1}.[g]=Fake.randG{2}.[(g, true, false)])/\
      (forall g (x:bool), g < Fake.n{2} + Fake.q{2} => g >= Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g >= Fake.n{2} + Fake.q{2} + Fake.g{2} => !in_dom (g, x) DKC.Dkc.r{1}) /\
      (forall g (x:bool), g < bound-1 => in_dom (g, x) DKC.Dkc.kpub{1} = in_dom (g, x) DKC.Dkc.kpub{2}) /\
    (!DKC.Dkc.b{1}) /\



      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} >= Fake.n{2} /\
      Fake.g{2} < Fake.n{2} + Fake.q{2}/\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      Fake.a{2} >= 0 /\
      Fake.b{2} >= 0 /\
      AdvAda.a{1} < Fake.g{2} /\
      AdvAda.b{1} < Fake.g{2} /\
      AdvAda.a{1} < bound-1 /\
      AdvAda.b{1} <= bound-1 /\
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

*)

  wp.
  while (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      getN AdvAda.fc{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      getM AdvAda.fc{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      getQ AdvAda.fc{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.q{2} >= Fake.m{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\

    AdvAda.i{1} = Fake.i{2} /\
      Fake.i{2} >= Fake.n{2} + Fake.q{2} - Fake.m{2} /\
    true
  );first (wp;skip;progress assumption;first (rewrite ! set_length;try assumption));smt.

  while (
      Fake.ev{2} = Garble.eval AdvAda.fc{1} AdvAda.xc{1} /\
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2}/\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      getN AdvAda.fc{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      getM AdvAda.fc{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      getQ AdvAda.fc{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      Fake.n{2} + Fake.q{2} - Fake.m{2} = bound /\
      AdvAda.l{1} = bound-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\ Fake.bb{2}.[i] < i /\
           Fake.bb{2}.[i] < bound /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\

    AdvAda.i{1} = Fake.i{2} /\
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
  delta queryValid.
  delta phi.
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

    cut rew : (length x1 = length x2);first smt.
    cut lem0 : (0 <= 0);first smt.
    cut lem1 : (0 >= 0);first smt.
    cut lem2 : (length x2 >= length x2);first smt.
    cut lem3 : (length x2 >= 1);first smt.
    cut lem4 : (0 <= length x2 + q2);first smt.

  generalize h.

  generalize bound.
  intros bound.

  subst;simplify.
  rewrite rew.

  progress ((try rewrite rew);(try apply init_length);(try rewrite rew);assumption).
  smt.
  smt.
  smt.
  smt.
  apply H48;smt.
  smt.
  smt.
  smt.
  smt.
  smt.
  apply H51;smt.
  smt.

  (*INVALID*)
  rcondf {1} 19;first (intros _;wp;rnd;wp;rnd;rnd;skip;smt).
  rcondf {2} 1;[intros &m;skip;smt|].
  wp.
  kill{1} 1!18;first (wp;rnd 1%r cpTrue;wp;rnd 1%r cpTrue;rnd 1%r cpTrue;skip;progress;smt).
  rnd;skip;progress assumption;smt.

save.
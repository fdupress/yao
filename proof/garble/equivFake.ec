require import Bitstring.
require import List.
require import Map.
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
  var v : bool array
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
    var tok : token;
    var zz : token;

    ttt = tweak g (t.[a]^^alpha) (t.[b]^^bet);
    input = (a, (t.[a]^^alpha));
    if (rand) {
      ra = $Dbool.dbool;
      output = (g + n + q, ra);
    } else
      output = (g, true (*TODO (evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^bet)))*));



    (*DKC encrypt*)
        tok = $DKC.genRandKey;
        ki = proj kpub.[input];
        zz = DKC.encode ttt (proj kpub.[input]) ksec tok;
    (*End DKC encrypt*)
     






    ans = sub ans 0 ((length ans) - 1);
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) zz;
    xx = setTok xx g (v.[a]^^alpha) ki;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) (DKC.encode
      (tweak g (t.[a]^^alpha) (t.[b]^^bet))
      (getTok xx a (v.[a]^^alpha))
      (getTok xx b (v.[b]^^alpha))
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
      v.[i] = eval f1 x1 i;
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < n+q) {
      v.[i] = eval f1 x1 i;
      t.[i] = false;
      i = i + 1;
    }


    t.[borne-1] = !tau;

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      if (b = borne - 1) {
        query(false, false, true);
        query(true, true, true);
        preGarbD(true, false);
      } else {
        preGarbD(true, false);
        preGarbD(false, true);
        preGarbD(true, true);
      }
      g = g + 1;
    }

    i = 0;
    while (i < n+q) {
      tok = $DKC.genRandKeyLast (! t.[i]);
      if (getTok xx i true = void /\ i <> 0) {
        xx = setTok xx i true tok;
      }
      tok = $DKC.genRandKeyLast (t.[i]);
      if (getTok xx i false = void) {
        xx = setTok xx i false tok;
      }
      i = i + 1;
    }

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      garb(getTok xx g v.[g], false, false);
      if (b <> borne - 1) {
        tok = garbD(false, true);
        tok = garbD(true, true);
        tok = garbD(true, false);
      } else {
        tok = garbD(true, false);
      }
      g = g + 1;
    }
    answer = ((getN f1, getM f1, getQ f1, getA f1, getB f1, pp), encrypt (Array.sub xx 0 (getN f1)) x1,tt);
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
      ksec = $DKC.genRandKeyLast tau;
      kpub = Map.empty;
      r = Map.empty;

      (f1, x1) = fst query;
      (n, m, q, aa, bb, gg) = f1;
      queries = Array.empty;
      t = Array.init (n+q) false;
      v = Array.init (n+q) false;
      xx = Array.init (n+q) (void, void);
      pp = Array.init (n+q) (void, void, void, void);
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


lemma fakeEq :
  forall (ADV <: Garble.Adv{AdvAda, DKC.Dkc, Fake}),
    equiv [
      GameAda(DKC.Dkc, ADV).work ~
      Fake(ADV).work
      : (glob ADV){1} = (glob ADV){2} /\
      (!DKC.Dkc.b{1}) /\ (AdvAda.l{1}=borne-1) ==> res{1} = res{2}
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

  swap{1} 8 -7.

  seq 1 1 : ((glob ADV){1} = (glob ADV){2}/\AdvAda.query{1} = Fake.query{2} /\ (!DKC.Dkc.b{1}) /\ (AdvAda.l{1}=borne-1)).
    call ((glob ADV){1} = (glob ADV){2}) (res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2});first (fun true;by progress).
  skip;progress;assumption.
  
  case (Garble.queryValid Fake.query{2}).

  (*VALID*)
  rcondt {1} 18;first (intros _;wp;rnd;wp;rnd;rnd;skip;progress assumption).
  rcondt {2} 1;first (intros &m;skip;by progress).

  swap{1} 8 -7.
  swap{2} 24 -23.

  wp.
  call ((glob ADV){1} = (glob ADV){2}/\answer{1}=answer{2}) (res{1}=res{2});first (fun true;by progress).
  wp.

  while (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2} /\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.v{1} = Fake.v{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      AdvAda.fc{1} = Fake.f1{2}/\
      (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
      AdvAda.xc{1} = Fake.x1{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      borne = Fake.n{2} + Fake.q{2} /\
      AdvAda.l{1} = borne-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\
           Fake.bb{2}.[i] < borne /\ Fake.bb{2}.[i] < i /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, if (AdvAda.bb{1}.[g] = borne-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true)) then
        AdvAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)] else true)/\

    AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} > Fake.n{2} /\
    true
  ).
    seq 6 6 : (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2} /\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.v{1} = Fake.v{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      AdvAda.fc{1} = Fake.f1{2}/\
      (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
      AdvAda.xc{1} = Fake.x1{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      borne = Fake.n{2} + Fake.q{2} /\
      AdvAda.l{1} = borne-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\
           Fake.bb{2}.[i] < borne /\ Fake.bb{2}.[i] < i /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, if (AdvAda.bb{1}.[g] = borne-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true)) then
        AdvAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)] else true)/\


    (if (AdvAda.b{1} = borne-1 /\ evalGate AdvAda.gg{1}.[Fake.g{2}]
      ((!AdvAda.v{1}.[AdvAda.a{1}]), false) = evalGate AdvAda.gg{1}.[Fake.g{2}] ((!AdvAda.v{1}.[AdvAda.a{1}]), true)) then
        AdvAda.yy{1}.[Fake.g{2}]=proj Fake.randG{2}.[(Fake.g{2}, true, false)] else true)/\
      AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} > Fake.n{2} /\
      AdvAda.a{1} = Fake.a{2} /\
      AdvAda.b{1} = Fake.b{2} /\
      AdvAda.a{1} < borne-1 /\
      AdvAda.b{1} <= borne-1 /\
      true
    );first (wp;skip;progress assumption;smt).
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
      (wp;skip;progress assumption;first rewrite H7);smt.
  

  wp.



  while (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2} /\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.v{1} = Fake.v{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      AdvAda.fc{1} = Fake.f1{2}/\
      (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
      AdvAda.xc{1} = Fake.x1{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      borne = Fake.n{2} + Fake.q{2} /\
      AdvAda.l{1} = borne-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\
           Fake.bb{2}.[i] < borne /\ Fake.bb{2}.[i] < i /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, if (AdvAda.bb{1}.[g] = borne-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true)) then
        AdvAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)] else true)/\

    AdvAda.i{1} = Fake.i{2} /\
      0 <= Fake.i{2} /\
    true
  ).
  wp.
  rnd.
  wp.
  rnd.
  skip.
  progress assumption;last 4 smt.
    delta setTok;simplify;rewrite ! set_length;try assumption;smt.
    smt.
    delta setTok;simplify;rewrite ! set_length;try assumption;smt.
  wp.

  while (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2} /\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.v{1} = Fake.v{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      AdvAda.fc{1} = Fake.f1{2}/\
      (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
      AdvAda.xc{1} = Fake.x1{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      borne = Fake.n{2} + Fake.q{2} /\
      AdvAda.l{1} = borne-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\
           Fake.bb{2}.[i] < borne /\ Fake.bb{2}.[i] < i /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\
    (forall g, if (AdvAda.bb{1}.[g] = borne-1 /\ evalGate AdvAda.gg{1}.[g]
      ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), false) = evalGate AdvAda.gg{1}.[g] ((!AdvAda.v{1}.[AdvAda.aa{1}.[g]]), true)) then
        AdvAda.yy{1}.[g]=proj Fake.randG{2}.[(g, true, false)] else true)/\

    AdvAda.g{1} = Fake.g{2} /\
      Fake.g{2} > Fake.n{2} /\
    true
  ).
    admit.

  wp.
  while (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2} /\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.v{1} = Fake.v{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      AdvAda.fc{1} = Fake.f1{2}/\
      (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
      AdvAda.xc{1} = Fake.x1{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      borne = Fake.n{2} + Fake.q{2} /\
      AdvAda.l{1} = borne-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\
           Fake.bb{2}.[i] < borne /\ Fake.bb{2}.[i] < i /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\

    AdvAda.i{1} = Fake.i{2} /\
      Fake.i{2} > 0 /\
    true
  );first (wp;skip;progress assumption;first (rewrite ! set_length;try assumption));smt.

  while (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
      AdvAda.xx{1} = Fake.xx{2} /\
      AdvAda.t{1} = Fake.t{2}/\
      AdvAda.v{1} = Fake.v{2}/\
      AdvAda.n{1} = Fake.n{2}/\
      AdvAda.m{1} = Fake.m{2}/\
      AdvAda.q{1} = Fake.q{2}/\
      AdvAda.aa{1} = Fake.aa{2}/\
      AdvAda.bb{1} = Fake.bb{2}/\
      AdvAda.randG{1} = Fake.randG{2}/\
      AdvAda.pp{1} = Fake.pp{2}/\
      AdvAda.fc{1} = Fake.f1{2}/\
      (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
      AdvAda.xc{1} = Fake.x1{2}/\
      Fake.n{2} > 1/\
      Fake.m{2} > 0/\
      Fake.q{2} > 0/\
      (*Fake.f1{2} = (Fake.n{2}, Fake.m{2}, Fake.q{2}, Fake.aa{2}, Fake.bb{2}, Fake.gg{2}) /\*)
      borne = Fake.n{2} + Fake.q{2} /\
      AdvAda.l{1} = borne-1 /\
    (forall i, i >= Fake.n{2} => i < Fake.n{2}+Fake.q{2} => Fake.aa{2}.[i] >= 0 /\
           Fake.bb{2}.[i] < borne /\ Fake.bb{2}.[i] < i /\ Fake.aa{2}.[i] < Fake.bb{2}.[i]) /\

    AdvAda.i{1} = Fake.i{2} /\
      Fake.i{2} > 0 /\
    true
  );first (wp;rnd;wp;skip;progress assumption;first (rewrite ! set_length;try assumption));smt.

  wp;rnd;rnd;rnd.
  skip.
  progress.

  (*INVALID*)
  rcondf {1} 18;first (intros _;wp;rnd;wp;rnd;rnd;skip;smt).
  rcondf {2} 1;[intros &m;skip;smt|].
  wp.
  kill{1} 1!17;first (wp;rnd 1%r cPtrue;wp;rnd 1%r cPtrue;rnd 1%r cPtrue;skip;progress;smt).
  rnd.*)
  skip;progress assumption.
save.
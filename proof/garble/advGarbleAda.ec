require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.
require import Array.

require import MyDkc.
require import Garble.
require import GarbleTools.

op eval(f:funct, i:input, k:int) = (evalComplete f i extract).[k].
op void = (Bitstring.zeros 0).

module AdvAda(A:Garble.Adv, Dkc:DKC.Dkc_t) (*: DKC.AdvAda*) = {

  var c : bool
  var fc : Garble.funct
  var xc : Garble.input
  var good : bool
  var tau : bool
  var l : int
  var queries : DKC.query array
  var ans : DKC.answer array
  var answer : Garble.functG*Garble.inputG*Garble.keyOutput
  var query : Garble.query

  var n : int
  var m : int
  var q : int
  var aa : w2g
  var bb : w2g
  var gg : bool g2v
  var pp : token g2v
  var t : bool array
  var v : bool array
  var yy : token array
  var xx : tokens
  var a : int
  var b : int
  var i : int
  var g : int

  fun query(rand:bool, alpha:bool, bet:bool) : token = {
    var ttt : token;
    var gamma : bool;
    var pos : bool;
    var input : int*bool;
    var output : int*bool;
    var ra : bool;
    var ki : token;
    var ko : token;
    var zz : token;
    ttt = tweak g (t.[a]^^alpha) (t.[b]^^bet);
    gamma = v.[g]^^(evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^alpha)));
    if (a = l) {
      pos = true;
      input = (b, (t.[b]^^bet));
    } else {
      pos = false;
      input = (a, (t.[a]^^alpha));
    }
    if (rand) {
      ra = $Dbool.dbool;
      output = (g + n + q, ra);
    } else
      output = (g, (t.[g]^^gamma));
    (ki, ko, zz) = Dkc.encrypt((input, output, pos, ttt));
    ans = sub ans 0 ((length ans) - 1);
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) zz;
    if (a=l)
      xx = setTok xx g (v.[b]^^bet) ki;
    else
      xx = setTok xx g (v.[a]^^alpha) ki;
    if (! rand)
      xx = setTok xx g (v.[g]^^gamma) ko;
    return ko;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) (DKC.encode
      (tweak g (t.[a]^^alpha) (t.[b]^^bet))
      (getTok xx a (v.[a]^^alpha))
      (getTok xx b (v.[b]^^alpha))
      yy);
  }

  fun garbD(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;
    if (rand)
      yy = $DKC.genRandKey;
    else
      yy = getTok xx g (evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^alpha)));
    garb(yy, alpha, bet);
    return yy;
  }

  fun garble() : unit = {
    var tok : token;
    var yyt : token;
    i = 0;
    while (i < n+q-1) {
      t.[i] = eval fc xc i;
      v.[i] = eval fc xc i;
      i = i + 1;
    }

    i = 0;
    while (i < n+q-m-1) {
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }

    t.[l] = !tau;

    g = n;
    while (g < n+q-1) {
      a = aa.[g];
      b = bb.[g];
      if (a = l) {
        tok = query(false, true, false);
        tok = query(false, true, true);
      }
      if (b = l) {
        tok = query(false, false, true);
        yy.[g] = query(true, true, true);
      }
      g = g + 1;
    }

    i = 0;
    while (i < n+q-1) {
      if (getTok xx i true = void /\ i <> 0) {
        tok = $DKC.genRandKeyLast (! t.[i]);
        xx = setTok xx i true tok;
      }
      if (getTok xx i false = void) {
        tok = $DKC.genRandKeyLast (t.[i]);
        xx = setTok xx i false tok;
      }
      i = i + 1;
    }

    g = n;
    while (g < n+q-1) {
      a = aa.[g];
      b = bb.[g];
      garb(getTok xx g v.[g], false, false);
      if (a <> l /\ b <> l) {
        tok = garbD(a <= l, true, false);
        tok = garbD(b <= l, false, true);
        yyt = garbD(a <= l, true, true);
        if (a <= l /\ l <= b /\ evalGate gg.[g] ((!v.[a]), false) = evalGate gg.[g] ((!v.[a]), true))
          garb(yyt, true, false);
      } else {
        if (a = l) {
          tok = garbD(false, false, true);
        } else {
          tok = garbD(true, true, false);
          if (evalGate gg.[g] ((!v.[a]), false) = evalGate gg.[g] ((!v.[a]), true))
            garb(yy.[g], true, false);
        }
      }
      g = g + 1;
    }
    answer = ((getN fc, getM fc, getQ fc, getA fc, getB fc, pp), encrypt (Array.sub xx 0 (getN fc)) xc,tt);
  }

  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 borne;
  }

  fun work(info:bool) : bool = {
    var challenge : bool;
    var ret : bool;
    query = A.gen_query();
    c = $Dbool.dbool;
    if (c) {
      fc = fst (fst query);
      xc = snd (fst query);
    } else {
      fc = fst (snd query);
      xc = snd (snd query);
    }
    (n, m, q, aa, bb, gg) = fc;
    queries = Array.empty;
    t = Array.init (n+q) false;
    v = Array.init (n+q) false;
    xx = Array.init (n+q) (void, void);
    yy = Array.init (n+q) void;
    gg = Array.init (n+q) (false, false, false, false);
    pp = Array.init (n+q) (void, void, void, void);
    tau = info;
    if (Garble.queryValid query)
    {
      garble();
      challenge = A.get_challenge(answer);
      ret = (c = challenge);
    }
    else
      ret = $Dbool.dbool;
    return ret;
  }
}.


  module GameAda(D:DKC.Dkc_t, Adv:Garble.Adv) = {

    module A = AdvAda(Adv, DKC.Dkc)

    fun preInit() : unit = {
      D.preInit();
      A.preInit();
    }

    fun work() : bool = {
      var info : bool;
      var advChallenge : bool;
      var realChallenge : bool;
      info = D.initialize();
      advChallenge = A.work(info);
      realChallenge = D.get_challenge();
      return advChallenge = realChallenge;
    }
    
    fun main() : bool = {
      var r : bool;
      preInit();
      r = work();
      return r;
    }
  }.

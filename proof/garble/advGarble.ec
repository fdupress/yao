require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.
require import Array.

require import Dkc.
require import Garble.
require import GarbleTools.

op eval(f:funct, i:input, k:int) = (evalComplete f i extract).[k].
op void = (Bitstring.zeros 0).

module Adv(A:Garble.Adv) : Dkc.Adv = {
  var c : bool
  var fc : Garble.funct
  var xc : Garble.input
  var good : bool
  var tau : bool
  var l : int
  var queries : Dkc.query array
  var ans : Dkc.answer array
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

  fun _query1(rand:bool, alpha:bool, bet:bool) : Dkc.query = {
    var ttt : token;
    var gamma : bool;
    var pos : bool;
    var input : int*bool;
    var output : int*bool;
    var ra : bool;
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
    return (input, output, pos, ttt);
  }

  fun _query2(rand:bool, alpha:bool, bet:bool, answer:Dkc.answer) : token = {
    var gamma : bool;
    var ki : token;
    var ko : token;
    var zz : token;
    gamma = v.[g]^^(evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^alpha)));
    (ki, ko, zz) = answer;
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) zz;
    if (a=l)
      xx = setTok xx g (v.[b]^^bet) ki;
    else
      xx = setTok xx g (v.[a]^^alpha) ki;
    if (! rand)
      xx = setTok xx g (v.[g]^^gamma) ko;
    return ko;
  }

  fun query1(rand:bool, alpha:bool, bet:bool) : unit = {
    var query:Dkc.query;
    query := _query1(rand, alpha, bet);
    queries = query::queries;
  }   

  fun query2(rand:bool, alpha:bool, bet:bool) : token = {
    var a:Dkc.answer;
    var r:token;
    a = ans.[(length ans) - 1];
    ans = sub ans 0 ((length ans) - 1);
    r := _query2(rand, alpha, bet, a);
    return r;
  }

  fun query(rand:bool, alpha:bool, bet:bool) : token = {
    var q:Dkc.query;
    var a:Dkc.answer;
    var r:token;
    q := _query1(rand, alpha, bet);
    (*a := DKC.encrypt(q);*)
    r := _query2(rand, alpha, bet, a);
    return r;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) (Dkc.encode
      (tweak g (t.[a]^^alpha) (t.[b]^^bet))
      (getTok xx a (v.[a]^^alpha))
      (getTok xx b (v.[b]^^alpha))
      yy);
  }

  fun garbD(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;
    if (rand)
      yy = $Dkc.genRandKey;
    else
      yy = getTok xx g (evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^alpha)));
    garb(yy, alpha, bet);
    return yy;
  }

  fun garble_queries() : unit = {
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
        query1(false, true, false);
        query1(false, true, true);
      }
      if (b = l) {
        query1(false, false, true);
        query1(true, true, true);
      }
      g = g + 1;
    }
  }

  fun garble_answer() : unit = {
    var tok : token;
    var yyt : token;

    g = n;
    while (g < n+q-1) {
      a = aa.[g];
      b = bb.[g];
      if (a = l) {
        tok := query2(false, true, false);
        tok := query2(false, true, true);
      }
      if (b = l) {
        tok := query2(false, false, true);
        yy.[g] := query2(true, true, true);
      }
      g = g + 1;
    }

    i = 0;
    while (i < n+q-1) {
      if (getTok xx i (!v.[i]) = void /\ i <> l) {
        tok = $Dkc.genRandKeyLast (! t.[i]);
        xx = setTok xx i (!v.[i]) tok;
      }
      if (getTok xx i (v.[i]) = void) {
        tok = $Dkc.genRandKeyLast (t.[i]);
        xx = setTok xx i (v.[i]) tok;
      }
      i = i + 1;
    }

    g = n;
    while (g < n+q-1) {
      a = aa.[g];
      b = bb.[g];
      garb(getTok xx g v.[g], false, false);
      if (a <> l /\ b <> l) {
        tok := garbD(a <= l, true, false);
        tok := garbD(b <= l, false, true);
        yyt := garbD(a <= l, true, true);
        if (a <= l /\ l <= b /\ evalGate gg.[g] ((!v.[a]), false) = evalGate gg.[g] ((!v.[a]), true))
          garb(yyt, true, false);
      } else {
        if (a = l) {
          tok := garbD(false, false, true);
        } else {
          tok := garbD(true, true, false);
          if (evalGate gg.[g] ((!v.[a]), false) = evalGate gg.[g] ((!v.[a]), true))
            garb(yy.[g], true, false);
        }
      }
      g = g + 1;
    }
    
  }

  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 borne;
  }

  fun gen_queries(info:bool) : Dkc.query array = {
    query := A.gen_query();
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
      garble_queries();
      good = true;
    }
    else
      good = false;
    return queries;
  }
  
  fun get_challenge(answers:Dkc.answer array) : bool = {
    var challenge : bool;
    var ret : bool;
    answers = answers;
    if (good)
    {
      garble_answer();
      challenge := A.get_challenge(answer);
      ret = (c = challenge);
    }
    else
      ret = $Dbool.dbool;
    return ret;
  }

}.

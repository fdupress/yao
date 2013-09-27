require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.
require import Array.

require import GarbleTools.

require import PreProof.

require import ReductionAda.

module Red(A:PrvIndSec.Adv_t) = {

  var c : bool
  var fc : funct
  var xc : input
  var good : bool
  var tau : bool
  var l : int
  var answer : functG*inputG*keyOutput
  var query : (PrvIndSec.Scheme.plain * PrvIndSec.Scheme.plain)

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
  var randG : (int*bool*bool, token) map
  var a : int
  var b : int
  var i : int
  var g : int

  var queries : DKCS.query array
  var answers : DKCS.answer array

  fun query1(rand:bool, alpha:bool, bet:bool) : DKCS.query = {
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
    gamma = v.[g]^^(evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^bet)));
    if (a = l) {
      pos = true;
      input = (b, (t.[b]^^bet));
    } else {
      pos = false;
      input = (a, (t.[a]^^alpha));
    }
    ra = $Dbool.dbool;
    if (rand) {
      output = (g + n + q, ra);
    } else
      output = (g, (t.[g]^^gamma));
    return (input, output, pos, ttt);
  }

  fun query2(rand:bool, alpha:bool, bet:bool, answer:DKCS.answer) : token = {
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
    gamma = v.[g]^^(evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^bet)));
    if (a = l) {
      pos = true;
      input = (b, (t.[b]^^bet));
    } else {
      pos = false;
      input = (a, (t.[a]^^alpha));
    }
    ra = $Dbool.dbool;
    if (rand) {
      output = (g + n + q, ra);
    } else
      output = (g, (t.[g]^^gamma));
    (ki, ko, zz) = answer;
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) zz;
    if (a=l)
      xx = setTok xx g bet ki;
    else
      xx = setTok xx g alpha ki;
    if (! rand)
      xx = setTok xx g gamma ko;
    return ko;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((t.[a]^^alpha), (t.[b]^^bet)) (DKC.encode
      (tweak g (t.[a]^^alpha) (t.[b]^^bet))
      (getTok xx a alpha)
      (getTok xx b bet)
      yy);
  }

  fun preGarbD(rand:bool, alpha:bool, bet:bool) : unit = {
    var yy : token;
    if (rand) randG.[(g,alpha,bet)] = $DKC.genRandKey;
  }

  fun garbD(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;
    if (rand)
      yy = proj randG.[(g,alpha,bet)];
    else
      yy = getTok xx g (evalGate gg.[g] ((v.[a]^^alpha),(v.[b]^^alpha)));
    garb(yy, alpha, bet);
    return yy;
  }

  fun garble1() : unit = {
    var tok : token;
    var yyt : token;
    var qu : DKCS.query;

    i = 0;
    while (i < n+q-m) {
      v.[i] = eval fc xc i;
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < n+q) {
      v.[i] = eval fc xc i;
      t.[i] = false;
      i = i + 1;
    }


    t.[l] = !tau;

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      if (a = l) {
        qu = query1(false, true, false);
        queries = qu::queries;
        qu = query1(false, true, true);
        queries = qu::queries;
      }
      if (b = l) {
        qu = query1(false, false, true);
        queries = qu::queries;
        qu = query1(true, true, true);
        queries = qu::queries;
      }
      g = g + 1;
    }
  }

  fun garble2() : unit = {
    var tok : token;
    var yyt : token;
    var answerInd : int;

    answerInd = 0;

    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      if (a = l) {
        tok = query2(false, true, false, answers.[answerInd]);
        answerInd = answerInd + 1;
        tok = query2(false, true, true, answers.[answerInd]);
        answerInd = answerInd + 1;
      }
      if (b = l) {
        tok = query2(false, false, true, answers.[answerInd]);
        answerInd = answerInd + 1;
        yy.[g] = query2(true, true, true, answers.[answerInd]);
        answerInd = answerInd + 1;
      }
      if (a <> l /\ b <> l) {
        preGarbD(a <= l, true, false);
        preGarbD(b <= l, false, true);
        preGarbD(a <= l, true, true);
      } else {
        if (a = l) {
          preGarbD(false, false, true);
        } else {
          preGarbD(true, true, false);
        }
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (! t.[g]);
      if (getTok xx g true = void) {
        xx = setTok xx g true tok;
      }
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (t.[g]);
      if (getTok xx g false = void) {
        xx = setTok xx g false tok;
      }
      }
      
      g = g + 1;
    }

    i = 0;
    while (i < n+q) {
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (! t.[i]);
      if (getTok xx i true = void /\ i <> l) {
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
      if (a <> l /\ b <> l) {
        tok = garbD(b <= l, false, true);
        yyt = garbD(a <= l, true, true);
        if (a < l /\ l < b /\ evalGate gg.[g] ((!v.[a]), false) = evalGate gg.[g] ((!v.[a]), true))
          garb(yyt, true, false);
        else
          tok = garbD(a <= l, true, false);
      } else {
        if (a = l) {
          tok = garbD(false, false, true);
        } else {
          if (evalGate gg.[g] ((!v.[a]), false) = evalGate gg.[g] ((!v.[a]), true))
            garb(yy.[g], true, false);
          else
            tok = garbD(true, true, false);
        }
      }
      g = g + 1;
    }
    answer = ((getN fc, getM fc, getQ fc, getA fc, getB fc, pp), encrypt (Array.sub xx 0 (getN fc)) (Array.create (getN fc) false),tt);
  }

  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 (Cst.bound-1);
  }

  fun gen_queries(info:bool) : DKCS.query array = {
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
    t = Array.create (n+q) false;
    v = Array.create (n+q) false;
    xx = Array.create (n+q) (void, void);
    yy = Array.create (n+q) void;
    pp = Array.create (n+q) (void, void, void, void);
    randG = Map.empty;
    tau = info;
    queries = Array.create 0 ((0, false), (0, false), false, void);
    garble1();
    return queries;
  }
  
  fun get_challenge(answers: (DKCS.answer array)) : bool = {
    var challenge : bool;
    var ret : bool; 
    if (PrvIndSec.Scheme.queryValid query)
    {
      Red.answers = answers;
      garble2();
      challenge = A.get_challenge(answer);
      ret = (c = challenge);
    }
    else
      ret = $Dbool.dbool;
    return ret;
  }
}.

lemma query1L (A <: PrvIndSec.Adv_t): islossless Red(A).query1.
proof strict.
by fun; do ?(wp; rnd); wp; skip; smt.
qed.

lemma garble1L (A <: PrvIndSec.Adv_t): islossless Red(A).garble1.
proof strict.
fun; while true (Red.n + Red.q - Red.g).
  intros=> z; wp; case (Red.aa.[Red.g] = Red.l).
    case (Red.bb.[Red.g] = Red.l); (rcondt 3; first by wp).
      by (rcondt 7; first by do !(wp; call (_: true ==> true)=> //); wp); do !(wp; call (query1L A)); wp; skip; smt.
      by (rcondf 7; first by do !(wp; call (_: true ==> true)=> //); wp); do !(wp; call (query1L A)); wp; skip; smt.
    case (Red.bb.[Red.g] = Red.l); (rcondf 3; first by wp).
      by (rcondt 3; first by wp); do !(wp; call (query1L A)); wp; skip; smt.
      by (rcondf 3; first by wp); wp; skip; smt.
wp; while true (Red.n + Red.q - Red.i);
  first by intros=> z; wp; skip; smt.
wp; while true (Red.n + Red.q - Red.m - Red.i);
  first by intros=> z; wp; rnd; wp; skip; smt.
by wp; skip; smt.
qed.
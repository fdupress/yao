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

op eval(f:funct, i:input, k:int) = (evalComplete f i extract).[k].
op void = (Bitstring.zeros 0).

(*
lemma eval_val : forall f x i,
  i >= (getN f) + (getQ f) - (getM f) => i < (getN f) + (getQ f) =>
  eval f x i = (Garble.eval f x).[i-((getN f) + (getQ f) - (getM f))] by admit.*)

(* This is chosen once and for all at the beginning of the experiment *)
module G = {
  var c:bool
  var good:bool
  var bad:bool
  var l:int
  var query : (PrvIndSec.Scheme.plain * PrvIndSec.Scheme.plain)
}.

(* This is the circuit to garble (fixed after the adversary runs and the challenge is chosen) *)
module C = {
  var fc:funct
  var xc:input
  var n:int
  var m:int
  var q:int
  var aa:w2g
  var bb:w2g
  var gg:bool g2v
}.

(* This is what actually gets written to during the course of the experiment and the adversary run *)
(* What Bellare Tung Hoand and Rogaway call the "private state" *)
module P = {
  var tau:bool
  var t:bool array
  var v:bool array
  var pp:token g2v
  var yy:token array
  var xx:tokens
  var randG: (int*bool*bool,token) map (* What's this? *)
  var a:int
  var b:int
  var i:int
  var g:int
  var answer : functG*inputG*keyOutput
}.
  

module RedAda(A:PrvIndSec.Adv_t, Dkc:DKCS.Dkc_t) = {
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

    ttt = tweak P.g (P.t.[P.a]^^alpha) (P.t.[P.b]^^bet);
    gamma = P.v.[P.g]^^(evalGate C.gg.[P.g] ((P.v.[P.a]^^alpha),(P.v.[P.b]^^bet)));
    if (P.a = G.l) {
      pos = true;
      input = (P.b, (P.t.[P.b]^^bet));
    } else {
      pos = false;
      input = (P.a, (P.t.[P.a]^^alpha));
    }

    ra = $Dbool.dbool;
    if (rand) output = (P.g + C.n + C.q, ra);
    else output = (P.g, (P.t.[P.g]^^gamma));

    (ki, ko, zz) = Dkc.encrypt((input, output, pos, ttt));
    P.pp.[P.g] = setGateVal P.pp.[P.g] ((P.t.[P.a]^^alpha), (P.t.[P.b]^^bet)) zz;
    if (P.a=G.l)
      P.xx = setTok P.xx P.g bet ki;
    else
      P.xx = setTok P.xx P.g alpha ki;
    if (! rand)
      P.xx = setTok P.xx P.g gamma ko;
    return ko;
  }

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    P.pp.[P.g] = setGateVal P.pp.[P.g] ((P.t.[P.a]^^alpha), (P.t.[P.b]^^bet)) (DKC.encode
      (tweak P.g (P.t.[P.a]^^alpha) (P.t.[P.b]^^bet))
      (getTok P.xx P.a alpha)
      (getTok P.xx P.b bet)
      yy);
  }

  fun preGarbD(rand:bool, alpha:bool, bet:bool) : unit = {
    var yy : token;
    if (rand) P.randG.[(P.g,alpha,bet)] = $DKC.genRandKey;
  }

  fun garbD(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;
    if (rand)
      yy = proj P.randG.[(P.g,alpha,bet)];
    else
      yy = getTok P.xx P.g (evalGate C.gg.[P.g] ((P.v.[P.a]^^alpha),(P.v.[P.b]^^alpha)));
    garb(yy, alpha, bet);
    return yy;
  }

  fun garble() : unit = {
    var tok : token;
    var yyt : token;

    P.i = 0;
    while (P.i < C.n + C.q - C.m) {
      P.v.[P.i] = eval C.fc C.xc P.i;
      P.t.[P.i] = $Dbool.dbool;
      P.i = P.i + 1;
    }
    while (P.i < C.n + C.q) {
      P.v.[P.i] = eval C.fc C.xc P.i;
      P.t.[P.i] = false;
      P.i = P.i + 1;
    }


    P.t.[G.l] = !P.tau;

    P.g = C.n;
    while (P.g < C.n + C.q) {
      P.a = C.aa.[P.g];
      P.b = C.bb.[P.g];
      if (P.a = G.l) {
        tok = query(false, true, false);
        tok = query(false, true, true);
      }
      if (P.b = G.l) {
        tok = query(false, false, true);
        P.yy.[P.g] = query(true, true, true);
      }
      if (P.a <> G.l /\ P.b <> G.l) {
        preGarbD(P.a <= G.l, true, false);
        preGarbD(P.b <= G.l, false, true);
        preGarbD(P.a <= G.l, true, true);
      } else {
        if (P.a = G.l) {
          preGarbD(false, false, true);
        } else {
          preGarbD(true, true, false);
        }
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (! P.t.[P.g]);
      if (getTok P.xx P.g true = void) {
        P.xx = setTok P.xx P.g true tok;
      }
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (P.t.[P.g]);
      if (getTok P.xx P.g false = void) {
        P.xx = setTok P.xx P.g false tok;
      }
      }
      
      P.g = P.g + 1;
    }

    P.i = 0;
    while (P.i < C.n + C.q) {
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (! P.t.[P.i]);
      if (getTok P.xx P.i true = void /\ P.i <> G.l) {
        P.xx = setTok P.xx P.i true tok;
      }
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok (P.t.[P.i]);
      if (getTok P.xx P.i false = void) {
        P.xx = setTok P.xx P.i false tok;
      }
      P.i = P.i + 1;
    }

    P.g = C.n;
    while (P.g < C.n + C.q) {
      P.a = C.aa.[P.g];
      P.b = C.bb.[P.g];
      garb(getTok P.xx P.g false, false, false);
      if (P.a <> G.l /\ P.b <> G.l) {
        tok = garbD(P.b <= G.l, false, true);
        yyt = garbD(P.a <= G.l, true, true);
        if (P.a < G.l /\ G.l < P.b /\ evalGate C.gg.[P.g] ((!P.v.[P.a]), false) = evalGate C.gg.[P.g] ((!P.v.[P.a]), true))
          garb(yyt, true, false);
        else
          tok = garbD(P.a <= G.l, true, false);
      } else {
        if (P.a = G.l) {
          tok = garbD(false, false, true);
        } else {
          if (evalGate C.gg.[P.g] ((!P.v.[P.a]), false) = evalGate C.gg.[P.g] ((!P.v.[P.a]), true))
            garb(P.yy.[P.g], true, false);
          else
            tok = garbD(true, true, false);
        }
      }
      P.g = P.g + 1;
    }
    P.answer = ((getN C.fc, getM C.fc, getQ C.fc, getA C.fc, getB C.fc, P.pp), encrypt (Array.sub P.xx 0 (getN C.fc)) (Array.create (getN C.fc) false),tt);
  }

  
  fun preInit() : unit = {
    G.l = $Dinter.dinter 0 (Cst.bound-1);
  }

  fun work(info:bool) : bool = {
    var challenge : bool;
    var ret : bool; 

    G.query = A.gen_query();
    G.c = $Dbool.dbool;
    if (G.c) {
      C.fc = fst (fst G.query);
      C.xc = snd (fst G.query);
    } else {
      C.fc = fst (snd G.query);
      C.xc = snd (snd G.query);
    }
    (C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.fc;
    P.t = Array.create (C.n + C.q) false;
    P.v = Array.create (C.n + C.q) false;
    P.xx = Array.create (C.n + C.q) (void, void);
    P.yy = Array.create (C.n + C.q) void;
    P.pp = Array.create (C.n + C.q) (void, void, void, void);
    P.randG = Map.empty;
    P.tau = info;
    if (PrvIndSec.Scheme.queryValid G.query)
    {
      garble();
      challenge = A.get_challenge(P.answer);
      ret = (G.c = challenge);
    }
    else
      ret = $Dbool.dbool;
    return ret;
  }
}.

module PreInit(ADV:PrvIndSec.Adv_t) = {
  module Ga = DKCS.GameAda(DKCS.Dkc, RedAda(ADV))

  fun f(vl:int, vb:bool) : bool = {
    var r : bool;
    G.l = vl;
    DKCS.Dkc.b = vb;
    r = Ga.work();
    return r;
  }
}.
require import Bitstring.
require import Int.
require import Map.
require import Pair.
require import Bool.
require import Array.

require import Dkc.
require import GarbleTools.
require import Scheme.

clone Scheme as Gate with
  type funct = bool*bool*bool*bool,
  type functG = token*token*token*token,
  type input = bool*bool,
  type output = bool,
  type keyInput = tokens,
  type keyOutput = unit,
  type inputG = token*token,
  type outputG = token,
  type tPhi = unit,

  type random = tokens,

  pred functCorrect(f:funct) = true,
  pred randomCorrect(f:funct, x:tokens) = tokenCorrect 2 1 1 x,
  pred inputCorrect(f:funct, i:input) = true,

  op phi(f:funct) = tt,
  op phiG(g:functG) = tt,

  op eval(f:funct, i:input) = evalGate f i,

  op garble(x:random, f:funct) =
    (garbleGate x f 0 1 2, x, tt),

  op encrypt(k:keyInput, i:input) =
    (getTok k 0 (fst i), getTok k 1 (snd i)),

  op decrypt(k:keyOutput, o:outputG) = lsb o,

  op evalG(g:functG, i:inputG) =
    let a = lsb (fst i) in
    let b = lsb (snd i) in
    let t = evalGate g (a, b) in
    Dkc.decode (tweak 2 a b) (fst i) (snd i) t.

export Gate.

lemma inverse :
  forall (f : funct) , functCorrect f =>
  forall (x : random) , randomCorrect f x =>
  forall (i : input) , inputCorrect f i =>
    let (g, ki, ko) = garble x f in
    eval f i = decrypt ko (evalG g (encrypt ki i))
proof.
  intros f fC x xC i iC.
  cut main : (
    let (g, ki, ko) = garble x f in
    evalG g (encrypt ki i) = getTok x 2 (eval f i)
  ).
    delta garble decrypt eval evalG encrypt.
    simplify.
  apply (inverse_base i 2 1 1 0 1 2 f x _ _ _ _ _ _ _);trivial.
  cut main2 : (let (g, ki, ko) = garble x f in
    eval f i = decrypt ko (getTok x 2 (eval f i)));trivial.
save.

module RandGate : Rand_t = {
  fun genT() : bool*bool = {
    var t0 : bool;
    var t1 : bool;
    t0 = $Dbool.dbool;
    t1 = $Dbool.dbool;
    return (t0, t1);
  }
    
  fun genR(t:bool*bool) : random = {
    var r : tokens;
    var r0f : token;
    var r0t : token;
    var r1f : token;
    var r1t : token;
    var r2f : token;
    var r2t : token;
    var t0,t1 : bool*bool = t;
    r0f = $Dkc.genRandKeyLast(t0);
    r1t = $Dkc.genRandKeyLast(!t0);
    r1f = $Dkc.genRandKeyLast(t1);
    r1t = $Dkc.genRandKeyLast(!t1);
    r2f = $Dkc.genRandKeyLast(false);
    r2t = $Dkc.genRandKeyLast(true);
    r = Array.empty:::(r0f, r0t):::(r1f, r1t):::(r2f, r2t);
    return r;
  }

  fun gen() : random = {
    var r : tokens;
    var t : bool*bool;
    t := genT();
    r := genR(t);
    return r;
  }
}.
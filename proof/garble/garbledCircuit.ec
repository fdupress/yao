require import Int.
require import Array.
require import Pair.
require import Bool.

require import Garble.
require import GarbleTools.
require import IND.

require Dkc.

theory Cst.
op bound : int.
axiom boundInf : bound > 1.
end Cst.
import Cst.

clone Dkc.DKC_Abs as DKC.

clone Garble as GarbleCircuit with

  (*Types*)
  type funct = bool functGen,
  type functG = token functGen,
  type input = bool array,
  type output = bool array,
  type keyInput = (token*token) array,
  type keyOutput = unit,
  type inputG = token array,
  type outputG = token array,
  type tPhi = int*int*int*w2g*w2g,
  
  type random = tokens,

  (*Correction predicat*)
  op functCorrect = validCircuit bound,
  op inputCorrect(f:funct, i:input) =
    (getN f) = Array.length i,
  pred randomCorrect(f:funct, x:tokens) =
    tokenCorrect (getN f) (getQ f) (getM f) x,

  (*Operator*)
  op phi(f:funct) =
    let (n, m, q, aa, bb, gg) = f in
    (n, m, q, aa, bb),

  op phiG(f:functG) =
    let (n, m, q, aa, bb, gg) = f in
    (n, m, q, aa, bb),

  op eval(f:funct, i:input) = evalGen f i extract,

  op evalG(f:functG, i:inputG) = evalGen f i extractG,

  op garble(x:tokens, f:funct) =
    let pp = init ((getN f)+(getQ f)) (garbMap x f) in
    let ff = ((getN f), (getM f), (getQ f), (getA f), (getB f), pp) in
    (ff, Array.sub x 0 (getN f), tt),

  op encrypt(k:keyInput, i:input) = init (Array.length i) (choose k i),
  
  op decrypt(k:keyOutput, o:outputG) = map lsb o.
export GarbleCircuit.

(*require import IND.*)

clone PrvInd as PrvInd_Circuit with
  theory Garble = GarbleCircuit.

clone IND as PrvIndSec with
  theory Scheme = PrvInd_Circuit.Scheme.

(*module RandGarble : PrvIndSec.Rand_t = {
  fun gen(query :funct*input) : random = {
    var i:int;
    var t:bool array;
    var xx : tokens;
    var tok : token;
    var f:funct;
    var x:input;

    t = Array.empty;
    xx = Array.empty;
    

    (f, x) = query;
    i = 0;
    while (i < (getN f)+(getQ f)-(getM f)-1) {
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < (getN f)+(getQ f)-1) {
      t.[i] = false;
      i = i + 1;
    }

    i = 0;
    while (i < (getN f)+(getQ f)-1) {
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok  (! t.[i]);
      xx = setTok xx i true tok;
      tok = $DKC.genRandKeyLast;
      tok = DKC.addLast tok t.[i];
      xx = setTok xx i false tok;
      i = i + 1;
    }
    return xx;
  }
}.*)
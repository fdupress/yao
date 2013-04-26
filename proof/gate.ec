require import Bitstring.
require import Int.
require import Map.
require import Pair.
require import Dkc.
require import GarbleTools.
require import Bool.

(*
require import Scheme.
clone Scheme as Gate with
  type funct = bool*bool*bool*bool,
  type functG = token*token*token*token,
  type input = bool*bool,
  type output = bool,
  type keyInput = token*token*token*token,
  type keyOutput = unit,
  type inputG = token*token,
  type outputG = bool,
  type random = tokens.
*)

theory Gate.

  type funct = bool*bool*bool*bool.
  type functG = token*token*token*token.
  type input = bool*bool.
  type output = bool.
  type keyInput = tokens.
  type keyOutput = unit.
  type inputG = token*token.
  type outputG = token.
  type phiT = unit.

  op phi : phiT = tt.

  op eval(f:funct, i:input) : output = evalGate f i.

  op _garble(x:tokens, f:funct) : functG*keyInput*keyOutput =
    (garbleGate x f 0 1 2, x, tt).
  
  pred tokenCorrect(x:tokens) = tokenCorrect 2 1 1 x.

  op encrypt(k:keyInput, i:input) : inputG =
    (getTok k 0 (fst i), getTok k 1 (snd i)).

  op decrypt(k:keyOutput, o:outputG) : output = lsb o.

  op evalG(g:functG, i:inputG) : outputG =
    let a = lsb (fst i) in
    let b = lsb (snd i) in
    let t = evalGate g (a, b) in
    Dkc.decode (tweak 2 a b) (fst i) (snd i) t.

  lemma inverse :
    forall (i : input) ,
    forall (f : funct) ,
    forall (x : tokens) ,
      tokenCorrect x =>
      let (g, ki, ko) = _garble x f in
      eval f i = decrypt ko (evalG g (encrypt ki i))
  proof.
  intros i f x.
  intros tokCor.
  cut main : (
    let (g, ki, ko) = _garble x f in
    evalG g (encrypt ki i) = getTok x 2 (eval f i)
  ).
  delta _garble decrypt eval evalG encrypt.
  simplify.
  apply (inverse_base i 2 1 1 0 1 2 f x _ _ _ _ _ _ _).
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  cut main2 : (let (g, ki, ko) = _garble x f in
    eval f i = decrypt ko (getTok x 2 (eval f i))).
  trivial.
  trivial.
  save.

end Gate.
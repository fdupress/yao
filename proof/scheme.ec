require import Real.
require import Pair.

theory Scheme.
  type funct.
  type functG.
  type input.
  type output.
  type keyInput.
  type keyOutput.
  type inputG.
  type outputG.
  type tPhi.
  
  type random.

  pred functCorrect : funct.
  pred randomCorrect : (funct, random).
  pred inputCorrect : (funct, input).

  op garble : random -> funct -> functG*keyInput*keyOutput.
  op encrypt : keyInput -> input -> inputG.
  op decrypt : keyOutput -> outputG -> output.
  op eval : funct -> input -> output.
  op evalG : functG -> inputG -> outputG.
  op phi : funct -> tPhi.
  op phiG : functG -> tPhi.

  axiom inverse :
    forall (f : funct) , functCorrect f =>
    forall (x : random) , randomCorrect f x =>
    forall (i : input) , inputCorrect f i =>
      let (g, ki, ko) = garble x f in
      eval f i = decrypt ko (evalG g (encrypt ki i)).

  type query = (funct*input)*(funct*input).
  type answer = functG*inputG*keyOutput.

  op bsample : bool distr.

  op k : int.

  module type GARBLE = {
    fun garb(query:query) : answer
    fun get_challenge() : bool
  }.

  module type Adv = {
    fun gen_query() : query
    fun get_challenge(answer:answer) : bool
  }.

  module type Rand_t = { fun gen() : random }.

  module PrvInd(Rand:Rand_t) : GARBLE = {
    var b : bool
  
    fun garb(query:query) : answer = {
      var f, f0, f1 : funct*funct*funct;
      var x, x0, x1 : input*input*input;
      var e : keyInput;
      var d : keyOutput;
      var g : functG;
      var y : inputG;
      var r : random;

      (* Phi test*)
      (* Input test *)
      (* if ((eval f0 x0) != (eval f1 x1)) fail *)
      (f0, x0) = fst query;
      (f1, x1) = snd query;
      b = $bsample;
      if (b) { x = x1;f = f1; } else {x=x0;f=f0;}
      r := Rand.gen();
      (g, e, d) = garble r f;
      y = encrypt e x;
      return (g, y, d);
    }

    fun get_challenge() : bool = {
      return b;
    }
  }.


  module Game(Garble:GARBLE, ADV:Adv) = {
    fun main() : bool = {
      var query : query;
      var answer : answer;
      var adv, real : bool*bool;
    
      query := ADV.gen_query();
      answer := Garble.garb(query);
      real := Garble.get_challenge();
      adv := ADV.get_challenge(answer);

      return (adv = real);
    }
  }.

end Scheme.
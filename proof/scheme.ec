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
  
  type random.

  op _garble : random -> funct -> functG*keyInput*keyOutput.
  op getRandom : unit -> random.
  op garble(f:funct) : functG*keyInput*keyOutput = _garble (getRandom tt) f.
  op encrypt : keyInput -> input -> inputG.
  op decrypt : keyOutput -> outputG -> output.
  op eval : funct -> input -> output.
  op evalG : functG -> inputG -> outputG.

  axiom inverse :
    forall (f : funct) ,
    forall (i : input) ,
      let (g, ki, ko) = garble f in
      eval f i = decrypt ko (evalG g (encrypt ki i)).

  type query = (funct*input)*(funct*input).
  type answer = functG*inputG*keyOutput.

  op bsample : bool distr.

  op k : int.

  module type GARBLE = {
    fun garble(q:query) : answer
    fun get_challenge() : bool
  }.

  module type Adv = {
    fun gen_query() : query
    fun get_challenge(answer:answer) : bool
  }.

  module PrvInd : GARBLE = {
    var b : bool
  
    fun garble(query:query) : answer = {
      var f, f0, f1 : funct*funct*funct;
      var x, x0, x1 : input*input*input;
      var e : keyInput;
      var d : keyOutput;
      var g : functG;
      var y : inputG;

      (* Phi test*)
      (* Input test *)
      (* if ((eval f0 x0) != (eval f1 x1)) fail *)
      (f0, x0) = fst query;
      (f1, x1) = snd query;
      b = $bsample;
      if (b) { x = x1;f = f1; } else {x=x0;f=f0;}
      (g, e, d) = garble f;
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
      answer := Garble.garble(query);
      adv := ADV.get_challenge(answer);
      real := Garble.get_challenge();

      return (adv = real);
    }
  }.
  
  axiom PrvInd :
    forall (epsilon:real),
    forall (ADV<:Adv),
    forall &m,
      (epsilon > 0%r) => (Pr[Game(PrvInd, ADV).main()@ &m:res] < epsilon).

end Scheme.
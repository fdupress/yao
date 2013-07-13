require import Real.
require import Pair.
require import Bool.
require import INDCPA.

theory Garble.
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

  op functCorrect : funct -> bool.
  op inputCorrect : funct -> input -> bool.
  pred randomCorrect : (funct, random).

  op garble : random -> funct -> functG*keyInput*keyOutput.
  op encrypt : keyInput -> input -> inputG.
  op decrypt : keyOutput -> outputG -> output.
  op eval : funct -> input -> output.
  op evalG : functG -> inputG -> outputG.
  op phi : funct -> tPhi.
  op phiG : functG -> tPhi.
end Garble.

theory Correct.
  clone import Garble.

  axiom Correct : forall (f:funct) (x:random) (i:input),
    functCorrect f =>
    randomCorrect f x =>
    inputCorrect f i =>
      let (g, ki, ko) = garble x f in
      eval f i = decrypt ko (evalG g (encrypt ki i)).
end Correct.

theory PrvInd.
  clone import Garble.

  clone INDCPA_Scheme with
    type query = funct*input,
    type answer = functG*inputG*keyOutput,
    type random = random,

    op queryValid(queries:query*query) =
      let query0 = fst queries in
      let query1 = snd queries in
      functCorrect (fst query0) /\ functCorrect (fst query1) /\
      inputCorrect (fst query0) (snd query0) /\ inputCorrect (fst query1) (snd query1) /\
      eval (fst query0) (snd query0) = eval (fst query1) (snd query1) /\
      phi (fst query0) = phi (fst query1),

    op work (q:query) (r:random) =
      let (f, x) = q in
      let (g, ki, ko) = garble r f in
      (g, encrypt ki x, ko).

end PrvInd.
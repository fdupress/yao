require import Bitstring.
require import Int.
require import Map.
require import Pair.

require import Scheme.
require import Dkc.

cnst unit : unit.

theory Gate.
  clone Scheme as Scheme.
  export Scheme.

  type token = Dkc.number.

  type funct = bool*bool*bool*bool.
  type functG = token*token*token*token.
  type input = bool*bool.
  type output = bool.
  type keyInput = token*token*token*token.
  type keyOutput = unit.
  type inputG = token*token.
  type outputG = bool.

  type tokens = (int*bool, Gate.token) map.

  type query = (funct*input)*(funct*input).
  type answer = functG*inputG*keyOutput.
  
  op tweak(a:bool, b:bool) : bitstring = a::(b::(zeros (k-2))).
  
  op eval(f:funct, i:input) : output =
    let (ff, ft, tf, tt) = f in
    let (i1, i2) = i in
    if (((i1=false) && (i2=false))) then ff else
    if (((i1=false) && (i2=true))) then ft else
    if (((i1=true) && (i2=false))) then tf else
    tt.

  op enc(x:tokens, f:funct, x1:bool, x2:bool) : token =
    Dkc.encode (tweak x1 x2) (proj x.[(1, x1)]) (proj x.[(2, x2)]) (proj x.[(3, eval f (x1,x2))]).
  op garble(x:tokens, f:funct) : functG*keyInput*keyOutput =
    (
      (enc x f false false, enc x f false true, enc x f true false, enc x f true true),
      (proj x.[(1, false)], proj x.[(1, true)], proj x.[(2, false)], proj x.[(2, true)]),
      unit
    ).
  (*pred tokenCorrect(x:tokens) =
    (to_array x.[(1, false)]).[0] != (to_array x.[(1, true)]).[0] &&
    (to_array x.[(2, false)]).[0] != (to_array x.[(2, true)]).[0] &&
    (to_array x.[(3, false)]).[0] == false &&
    (to_array x.[(3, false)]).[0] == true.*)

  op encrypt(k:keyInput, i:input) : inputG =
    let (f1, t1, f2, t2) = k in
    let x1 = if fst i then t1 else f1 in
    let x2 = if snd i then t2 else f2 in
    (x1, x2).

  op decrypt(k:keyOutput, o:outputG) : output = o.

  op evalG(g:functG, i:inputG) : outputG =
    let (ff, ft, tf, tt) = g in
    let a = (fst i).[0] in
    let b = (snd i).[0] in
    let t =
      if (a = false) && (b = false) then ff else
      if (a = false) && (b = true) then ft else
      if (a = true) && (b = false) then tf else
      tt in
    let u = Dkc.decode (tweak a b) (fst i) (snd i) t in
    u.[0] (* C'est moche mais j'ai pas trouvé d'autre solution, c'est pas terrible*)
    .
    
  lemma inverse :
    forall (f : funct) ,
    forall (i : input) ,
    forall (x : tokens) ,
      let (g, ki, ko) = garble x f in
      eval f i = decrypt ko (evalG g (encrypt ki i)).
end Gate.
require import Bitstring.
require import Int.
require import Map.
require import Scheme.

theory Gate.
  clone Scheme as Scheme.
  export Scheme.

  type token = bitstring.

  type funct = bool*bool*bool*bool.
  type functG = ((bool*bool), token) map.
  type input = bool*bool.
  type output = bool.
  type keyInput = token*token*token*token.
  type keyOutput = unit.
  type inputG = token*token.
  type outputG = token.
  
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
end Gate.
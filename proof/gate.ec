require import Bitstring.
require import Int.
require import Map.
require import Pair.
require import Scheme.
require import Dkc.

op lsb(b:bitstring) : bool = b.[0].

op fst(x:'a*'b*'c) : 'a = let (a, b, c) = x in a.
op snd(x:'a*'b*'c) : 'b = let (a, b, c) = x in b.
op thi(x:'a*'b*'c) : 'c = let (a, b, c) = x in c.

type token = Dkc.number.
type tokens = (int*bool, token) map.

op tweak(a:bool, b:bool) : bitstring = a::(b::(zeros (Scheme.k-2))).

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

(*
theory Gate.
  type token = Dkc.number.
  type tokens = (int*bool, Gate.token) map.

  type funct = bool*bool*bool*bool.
  type functG = token*token*token*token.
  type input = bool*bool.
  type output = bool.
  type keyInput = token*token*token*token.
  type keyOutput = unit.
  type inputG = token*token.
  type outputG = bool.
  
  op eval(f:funct, i:input) : output =
    let (ff, ft, tf, tt) = f in
    let (i1, i2) = i in
    if !i1 && !i2 then ff else
    if !i1 && i2 then ft else
    if  i1 && !i2 then tf else
    tt.

  op enc(x:tokens, f:funct, x1:bool, x2:bool) : token =
    let xx1 = (lsb (proj x.[(1, true)]) = x1) in
    let xx2 = (lsb (proj x.[(2, true)]) = x2) in
    Dkc.encode
      (tweak x1 x2)
      (proj x.[(1, xx1)])
      (proj x.[(2, xx2)])
      (proj x.[(3, eval f (xx1,xx2))]).
  op _garble(x:tokens, f:funct) : functG*keyInput*keyOutput =
    (
      (enc x f false false, enc x f false true, enc x f true false, enc x f true true),
      (proj x.[(1, false)], proj x.[(1, true)], proj x.[(2, false)], proj x.[(2, true)]),
      tt
    ).
  pred tokenCorrect(x:tokens) =
    (lsb (proj x.[(1, false)]) <> lsb (proj x.[(1, true)])) /\
    (lsb (proj x.[(2, false)]) <> lsb (proj x.[(2, true)])) /\
    (lsb (proj x.[(3, false)]) = false) /\
    (lsb (proj x.[(3, true )]) = true).

  op encrypt(k:keyInput, i:input) : inputG =
    let (f1, t1, f2, t2) = k in
    let x1 = if fst i then t1 else f1 in
    let x2 = if snd i then t2 else f2 in
    (x1, x2).

  op decrypt(k:keyOutput, o:outputG) : output = o.

  op evalG(g:functG, i:inputG) : outputG =
    let (ff, ft, tf, tt) = g in
    let a = lsb (fst i) in
    let b = lsb (snd i) in
    let t =
      if !a && !b then ff else
      if !a &&  b then ft else
      if  a && !b then tf else
      tt in
    lsb (Dkc.decode (tweak a b) (fst i) (snd i) t).

  lemma oparg :
    forall (f : 'a -> 'b),
    forall (x : 'a),
    forall (y : 'a),
      (x = y) => (f x = f y).

  lemma inverse :
    forall (i : input) ,
    forall (f : funct) ,
    forall (x : tokens) ,
     let i1 = fst i in
     let i2 = snd i in
      tokenCorrect x =>
      let temp = _garble x f in
      let g = fst temp in
      let ki = snd temp in
      let ko = thi temp in
      eval f (i1, i2) = decrypt ko (evalG g (encrypt ki (i1, i2)))
  proof.

  intros i f x i1 i2 tC g ki ko;
  delta decrypt evalG encrypt g ki ko tC _garble Pair.fst Pair.snd fst snd.

  case (i1).
  case (i2).

  simplify.
  case (lsb (proj x.[(1, true)])).
  simplify.
  trivial.
  simplify.
  trivial.

  simplify.
  case (lsb (proj x.[(1, true)])).
  simplify.
  trivial.
  simplify.
  trivial.

  case (i2).

  simplify.
  case (lsb (proj x.[(1, false)])).
  simplify.
  trivial.
  simplify.
  trivial.

  simplify.
  case (lsb (proj x.[(1, false)])).
  simplify.
  trivial.
  simplify.
  trivial.
  save.

end Gate.*)
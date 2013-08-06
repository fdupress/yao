require import Int.
require import Real.

require import Dkc.

op myK : int.
axiom mykVal : myK > 1.
clone Dkc.DKC as DKC with op k = myK.

op bound : int.
axiom boundInf : bound > 1.

axiom DkcCorrect :
  forall (t:DKC.tweak) (k1 k2:DKC.key) (m:DKC.msg),
    DKC.decode t k1 k2 (DKC.encode t k1 k2 m) = m.

axiom DkcSecure :
  exists (epsilon:real), epsilon > 0%r /\
    forall (A<:DKC.Adv_t), forall &m,
      `|2%r * Pr[DKC.Game(DKC.Dkc, A).main()@ &m:res] - 1%r| < epsilon.
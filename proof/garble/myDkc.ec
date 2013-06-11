require Dkc.
require import Int.

op myK : int.

axiom mykVal : myK > 1.

clone Dkc.DKC as DKC with op k = myK.

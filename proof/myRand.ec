require import Bool.
require import Bitstring.
require import Pair.
require import Distr.
require import Int.

theory Dbitstringlast.
  op dbitstringlast : int -> bool -> bitstring distr.
(*
  op _internal = Dprod.dprod (Dbitstring.dbitstring (k-1)) (Dunit.dunit v).
*)

  axiom mu_weight : forall (k:int) v, k > 1 =>
     mu_weight (dbitstringlast k v) = 1%r.
    
end Dbitstringlast.

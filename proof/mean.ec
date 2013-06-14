require import Set.
require import Real.
require import Distr.
require import Myset.

theory Mean.
  type base.

  op d : base distr.
  op support : base set.
  axiom in_support :
    forall (x:base),
      in_supp x d <=> mem x support.
  
  module type Worker = {
    fun work(x:base) : bool
  }.

  module Rand(W:Worker) = {
    fun randAndWork() : bool = {
      var r : bool;
      var x : base;
      x = $d;
      r = W.work(x);
      return r;
    }
  }.

  axiom Mean :
    forall &m,
      forall (W<:Worker),
        Pr[Rand(W).randAndWork()@ &m:res] =
          sum (lambda (x:base), (mu_x d x)*Pr[W.work(x)@ &m:res]) support.

  axiom Not :
    forall &m,
      forall (W<:Worker),
        forall x,
          Pr[W.work(x)@ &m:res] = 1%r - Pr[W.work(x)@ &m: !res].
end Mean.

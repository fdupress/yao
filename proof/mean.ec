require import FSet.
require import Real.
require import Distr.

require Monoid.
clone Monoid as MReal with
  type t = real,
  op Z = 0%r,
  op (+) = Real.(+)
  proof * by smt.

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
          MReal.SumSet.sum (lambda (x:base), (mu_x d x)*Pr[W.work(x)@ &m:res]) support.
end Mean.

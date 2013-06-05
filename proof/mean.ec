require import Set.
require import Real.
require import Distr.

op fold_right : ('a -> 'b -> 'b) -> 'b -> 'a set -> 'b.
axiom fold_nil: forall (e:'b) (f:'a -> 'b -> 'b),
  fold_right f e Set.empty = e.
axiom fold_cons: forall (e:'b) (f:'a -> 'b -> 'b) xs,
  let x = Set.pick xs in
  fold_right f e xs = f x (fold_right f e (Set.rm x xs)).

theory Mean.
  type base.

  op d : base distr.
  op support : base set.
  axiom in_support :
    forall (x:base, d:base distr),
      in_supp x d <=> mem x support.
  
  module type Worker = {
    fun work(x:base) : bool
  }.

  module Rand(W:Worker) = {
    fun randAndWork() : bool = {
      var r : bool;
      var x : base;
      x = $d;
      r := W.work(x);
      return r;
    }
  }.

  axiom Mean :
    forall &m,
      forall (W<:Worker),
        Pr[Rand(W).randAndWork()@ &m:res] = fold_right
          (lambda (x:base, sum:real), sum + (mu_x d x)*Pr[W.work(x)@ &m:res])
          (0%r)
          support.
end Mean.
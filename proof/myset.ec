require import Set.
require import Real.
require import Distr.

op fold_right : ('a -> 'b -> 'b) -> 'b -> 'a set -> 'b.
axiom fold_nil: forall (e:'b) (f:'a -> 'b -> 'b),
  fold_right f e Set.empty = e.
axiom fold_cons: forall (e:'b) (f:'a -> 'b -> 'b) xs,
  let x = Set.pick xs in
  fold_right f e xs = f x (fold_right f e (Set.rm x xs)).
axiom fold_cons2: forall (e:'b) (f:'a -> 'b -> 'b) xs x,
  fold_right f e (add x xs) = f x (fold_right f e xs).

op sum(f:'a -> real, s:'a set) : real =
  fold_right (lambda (x:'a, sum:real), sum + f x) (0%r) s.

lemma sum_in :
  forall (f:'a -> real) (s:'a set),
  sum f s = sum (lambda x, if mem x s then f x else 0%r) s.
proof.
admit.
save.

lemma sum_add :
  forall (f:'a -> real) (g:'a -> real) (s:'a set),
  (sum f s) + (sum g s) = sum (lambda x, f x + g x) s.
proof.
admit.
save.

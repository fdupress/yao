require import Set.
require import Real.
require import Distr.

op map : ('a -> 'b) -> 'a set -> 'b set.
axiom map_nil: forall (f:'a -> 'b),
  map f Set.empty = Set.empty.
axiom map_cons: forall (f:'a -> 'b) xs x,
  mem x xs =>
  map f xs = add (f x) (map f (rm x xs)).

op fold_right : ('a -> 'b -> 'b) -> 'b -> 'a set -> 'b.
axiom fold_nil: forall (f:'a -> 'b -> 'b) (e:'b),
  fold_right f e Set.empty = e.
axiom fold_rm: forall (f:'a -> 'b -> 'b) (e:'b) xs x,
  mem x xs =>
    fold_right f e xs = f x (fold_right f e (Set.rm x xs)).


lemma mem_rm: forall (y:'a) (x:'a) (S:'a set),
  x <> y =>
  mem y (rm x S) = mem y S by [].

lemma rm_add: forall (x:'a) (xs:'a set),
  !(mem x xs) =>
  rm x (add x xs) = xs by (intros _ _ _;apply Set.extensionality;trivial).

lemma _map_add: forall (f:'a -> 'b) x xs,
  !(mem x xs) =>
  map f (add x xs) = add (f x) (map f xs).
  intros f x xs h.
  rewrite (map_cons<:'b, 'a> f (add x xs) x _);first trivial.
  rewrite (_ : rm x (add x xs) = xs);first trivial.
  split.
save.

lemma mem_map: forall (f:'a -> 'b) x xs,
  mem x xs => mem (f x) (map f xs) by (intros _ _ S;elimT Set_ind S;trivial).

lemma map_add: forall (f:'a -> 'b) x xs,
  map f (add x xs) = add (f x) (map f xs).
  intros f x xs.
  case (mem x xs);last (apply _map_add;first assumption).
  intros hh.
  rewrite <- (mem_add<:'a> x xs _);first assumption.
  rewrite <- (mem_add<:'b> (f x) (map f xs) _);trivial.
save.

lemma mem_map_bij: forall (f:'a -> 'b) x xs,
  (forall x y, f x = f y => x = y) =>
  mem x xs = mem (f x) (map f xs) by (intros _ _ S _;elimT Set.Set_ind S;trivial).

lemma fold_add1: forall (f:'a -> 'b -> 'b) (e:'b) xs x,
  !mem x xs =>
    fold_right f e (add x xs) = f x (fold_right f e xs).
  intros e f xs x.
  rewrite (fold_rm<:'b, 'a> e f (add x xs) x _).
  apply (add_mem x x xs).
  intros h.
  rewrite (rm_add<:'a> x xs _);[assumption|split].
save.

lemma fold_add2: forall (f:'a -> 'b -> 'b) (e:'b) xs x,
  mem x xs =>
    fold_right f e (add x xs) = fold_right f e xs by [].



op sum(f:'a -> real, s:'a set) : real =
  fold_right (lambda (x:'a, sum:real), sum + f x) (0%r) s.

lemma sum_nil:
  forall (f:'a -> real), sum f Set.empty = 0%r by [].

lemma sum_rm :
  forall (f:'a -> real) (s:'a set) (x:'a),
  mem x s =>
  sum f s = (f x) + (sum f (rm x s)) by [].

lemma sum_add :
  forall (f:'a -> real) (s:'a set) (x:'a),
  (!mem x s) =>
  sum f (add x s) = (f x) + (sum f s) by [].

lemma sum_in :
  forall (f:'a -> real) (s:'a set),
  sum f s = sum (lambda x, if mem x s then f x else 0%r) s.
proof.
  delta sum.
  simplify.
  intros f s.
  apply (Set.Set_ind
(lambda S, S <= s => (
fold_right (lambda (x : 'a) (sum : real), sum + f x) 0%r S =
fold_right
  (lambda (x : 'a) (sum : real), sum + if mem x s then f x else 0%r) 0%r
  S)
) _ _ s);first trivial.
intros x S h hh hhh.
simplify.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S x _);first assumption.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + if mem x0 s then f x0 else 0%r) 0%r S x _);first assumption.
simplify.
rewrite (hh _);first trivial.
cut lem : (mem x s = true);first trivial.
rewrite lem.
simplify.
split.
save.

lemma sum_add2 :
  forall (f:'a -> real) (g:'a -> real) (s:'a set),
  (sum f s) + (sum g s) = sum (lambda x, f x + g x) s.
proof.
intros f g s.
delta sum.
elimT Set_ind s;first trivial.
intros x S h hh.
simplify.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S x _);first assumption.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + g x0) 0%r S x _);first assumption.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + (f x0 + g x0)) 0%r S x _);first assumption.
simplify.
rewrite <- hh.
generalize (fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S).
generalize (fold_right (lambda (x0 : 'a) (sum : real), sum + g x0) 0%r S).
intros a b.
trivial.
save.

lemma sum_chind :
  forall (f:'a -> real) (g:'a -> 'a) (gg:'a -> 'a) (s:'a set),
    (forall x, g (gg x) = x /\ gg (g x) = x) => (*TROP FORT ?*)
  (sum f s) = sum (lambda x, f (gg x)) (map g s).
proof.
intros f g gg s bij.
delta sum.
simplify.
  apply (Set.Set_ind
(lambda S, S <= s => (
fold_right (lambda (x : 'a) (sum : real), sum + f x) 0%r S =
fold_right (lambda (x : 'a) (sum : real), sum + f (gg x)) 0%r (map g S)
)) _ _ s);first trivial.
intros x S h hh.
simplify.
intros hhh.
rewrite (_:map g (add x S) = add (g x) (map g S));first trivial.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S x _);first assumption.
rewrite (fold_add1<:real,'a> (lambda (x0 : 'a) (sum : real), sum + f (gg x0)) 0%r (map g S) (g x) _);first (rewrite <- (mem_map_bij<:'a, 'a> g x S _);[trivial|assumption]).
simplify.
rewrite <- (hh _);first trivial.
rewrite (_:gg (g x)=x);first trivial.
split.
save.

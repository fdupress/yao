require import Set.
require import Real.
require import Distr.

lemma mem_rm: forall (y:'a) (x:'a) (S:'a set),
  x <> y =>
  mem y (rm x S) = mem y S by [].

lemma mem_map: forall (f:'a -> 'b) xs x,
  Set.mem x xs =>
  Set.mem (f x) (map f xs).
intros f S x;elimT Set.Induction.induction_det S;first smt.
simplify.
intros S0 hrec h.
rewrite (map_cons<:'b,'a> f S0).
smt.
save.


lemma mem_map_rev: forall (f:'a -> 'b) xs x,
  Set.mem (f x) (Set.map f xs) =>
  (exists y, f x = f y /\ Set.mem y xs)
by (intros _ S _;elimT Set.Induction.induction_det S;smt).

(*
lemma _map_add: forall (f:'a -> 'b) x xs,
  !(mem x xs) =>
  map f (add x xs) = add (f x) (map f xs).
  intros f x xs h.
  rewrite (map_cons<:'b, 'a> f (add x xs));first smt.
  rewrite (_ : rm x (add x xs) = xs);first smt.
  split.
save.
*)

(*
lemma map_add: forall (f:'a -> 'b) xs,
  let x = pick xs in
  map f (add x xs) = add (f x) (map f xs).
  intros f x xs.
  case (mem x xs);last (apply _map_add;first assumption).
  intros hh.
  rewrite <- (mem_add<:'a> x xs _);first assumption.
  rewrite <- (mem_add<:'b> (f x) (map f xs) _);smt.
save.
*)

(*
lemma mem_map_bij: forall (f:'a -> 'b) x xs,
  (forall x y, f x = f y => x = y) =>
  mem x xs = mem (f x) (map f xs) by (intros _ _ S _;elimT Set.Set_ind S;smt).
*)

require List.


op remove(x:'a, l:'a List.list) = List.filter (lambda y, x <> y) l.

lemma rem : forall (x:'a) l, List.mem x (remove x l) = false by [].

lemma rem_cons : forall (x:'a) l, !List.mem x l => remove x (List.(::) x l) = l.
intros x l.
delta remove.
simplify.
rewrite (List.filter_cons<:'a> (lambda (y : 'a), !(x = y)) x l).
simplify.
elimT List.list_ind l.
smt.
simplify.
intros y xs hrec h.
rewrite (List.filter_cons<:'a> (lambda (y : 'a), !(x = y)) y xs).
simplify.
rewrite (_ : ((!(x = y)) = true));first smt.
simplify.
rewrite (hrec _);first smt.
split.
save.


op enum(s:'a set) : 'a List.list = fold_right List.(::) (List.__nil) s.

pred eq (x y:'a List.list) = forall a, List.mem a x = List.mem a y.

lemma mem_enum : forall x (s:'a set), mem x s = List.mem x (enum s).
  intros x s.
  elimT Induction.induction_det s.
  smt.
  delta enum.
  simplify.
  intros S h.
  rewrite (fold_rm<:'a List.list, 'a> List.(::) List.__nil S).
  smt.
save.

lemma mem_fold_rm : forall x (s:'a set), !(List.mem x (enum (rm x s))) by [].

lemma enum : forall (s t:'a set), s == t <=> eq (enum s) (enum t) by [].

lemma enum_rm : forall (s:'a set) x, eq (enum (rm x s)) (remove x (enum s)).
admit.
save.

lemma rem_cons2 : forall (x:'a) l, List.mem x l => eq (List.(::) x (remove x l)) l.
delta eq.
smt.
save.

lemma exist : forall (l:'a List.list), exists (s:'a set), enum s = l.
admit.
save.
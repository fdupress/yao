require import Set.
require import Real.
require import Distr.

lemma mem_rm: forall (y:'a) (x:'a) (S:'a set),
  x <> y =>
  mem y (rm x S) = mem y S by [].

(*
lemma mem_map: forall (f:'a -> 'b) xs x,
  mem x xs =>
  mem (f x) (map f xs) by (intros _ S x _;elimT induction_det S;trivial).*)

(*
lemma _map_add: forall (f:'a -> 'b) x xs,
  !(mem x xs) =>
  map f (add x xs) = add (f x) (map f xs).
  intros f x xs h.
  rewrite (map_cons<:'b, 'a> f (add x xs));first trivial.
  rewrite (_ : rm x (add x xs) = xs);first trivial.
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
  rewrite <- (mem_add<:'b> (f x) (map f xs) _);trivial.
save.
*)

(*
lemma mem_map_bij: forall (f:'a -> 'b) x xs,
  (forall x y, f x = f y => x = y) =>
  mem x xs = mem (f x) (map f xs) by (intros _ _ S _;elimT Set.Set_ind S;trivial).
*)

require List.

op remove(x:'a, l:'a List.list) = List.filter (lambda y, x <> y) l.

lemma rem : forall (x:'a) l, List.mem x (remove x l) = false by [].

lemma rem_cons : forall (x:'a) l, !List.mem x l => remove x (List.(::) x l) = l by admit.

op enum(s:'a set) : 'a List.list = fold_right List.(::) (List.__nil) s.

pred eq (x y:'a List.list) = forall a, List.mem a x = List.mem a y.

lemma mem_fold_rm : forall x (s:'a set), !(List.mem x (enum (rm x s))).
intros x s.
delta enum.
simplify.
elimT Induction.induction s.
trivial.
simplify.
intros y S h.
case (x = y).
trivial.
rewrite <- (List.mem_cons<:'a> x (fold_right List.(::) List.__nil (rm x (add y S)))).
rewrite (fold_rm<:'a List.list, 'a> List.(::) List.__nil (rm x S)).

trivial.
lemma enum_rm : forall (s:'a set), let x = pick s in eq (enum (rm x s)) (remove x (enum s)).
intros s.
delta eq.
simplify.
intros a.
delta enum.
simplify.
rewrite (fold_rm<:'a List.list, 'a> List.(::) List.__nil s).
rewrite (rem_cons<:'a> (pick s) (fold_right List.(::) List.__nil (rm (pick s) s)) _).

admit.
split.
save.


(*
lemma fold_set_list : forall (f:'a -> 'b -> 'b) (e:'b) (s:'a set),
  fold_right f e s = List.fold_right f e (set_to_list s).
intros f e s.
elimT Induction.induction_det s;first trivial.
delta set_to_list.
simplify.
intros S h.
rewrite (fold_rm<:'a List.list,'a> List.(::) List.__nil S).
rewrite (fold_rm<:'b,'a> f e S).
rewrite h.
rewrite (List.fold_right_cons<:'b, 'a> e f (pick S) (fold_right List.(::) List.__nil (rm (pick S) S))).
split.
save.
*)

op sum(f:'a -> real, s:'a set) : real =
  List.fold_right (lambda (x:'a, sum:real), sum + f x) (0%r) (enum s).

lemma sum_nil:
  forall (f:'a -> real), sum f Set.empty = 0%r by [].

lemma sum_rm :
  forall (f:'a -> real) (s:'a set) (x:'a),
  mem x s =>
  sum f s = (f x) + (sum f (rm x s)).
intros f s x h.
delta sum.
simplify.
  apply (Induction.induction
(lambda S, S <> empty => S <= s => (
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S =
f x +
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r (rm x S)
)) _ _ s _);first trivial.
simplify.
intros y S h1 h2 h3 h4.
trivial.

cut lem : (S <> empty =>
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S =
f x +
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r (rm x S)).

elimT Induction.induction S.
trivial.
intros x0 S0 hh hhh hhhh.
trivial.


(*
lemma sum_add :
  forall (f:'a -> real) (s:'a set) (x:'a),
  (!mem x s) =>
  sum f (add x s) = (f x) + (sum f s) by [].
*)

lemma sum_in :
  forall (f:'a -> real) (s:'a set),
  sum f s = sum (lambda x, if mem x s then f x else 0%r) s.
proof.
  delta sum.
  simplify.
  intros f s.
  apply (Induction.induction_det
(lambda S, S <= s => (
fold_right (lambda (x : 'a) (sum : real), sum + f x) 0%r S =
fold_right
  (lambda (x : 'a) (sum : real), sum + if mem x s then f x else 0%r) 0%r
  S)
) _ _ s);first trivial.
simplify.
intros S h hh.
rewrite (fold_rm<:real,'a> (lambda (x : 'a) (sum : real), sum + f x) 0%r S).
rewrite (fold_rm<:real,'a> (lambda (x : 'a) (sum : real), sum + if mem x s then f x else 0%r) 0%r S).
simplify.
rewrite (h _);first trivial.
cut lem : (mem (pick S) s = true);first trivial.
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
elimT Induction.induction_det s;first trivial.
simplify.
intros S h.
rewrite (fold_rm<:real,'a> (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S).
rewrite (fold_rm<:real,'a> (lambda (x0 : 'a) (sum : real), sum + g x0) 0%r S).
rewrite (fold_rm<:real,'a> (lambda (x0 : 'a) (sum : real), sum + (f x0 + g x0)) 0%r S).
simplify.
rewrite <- h.
generalize (fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r (rm (pick S) S)).
generalize (fold_right (lambda (x0 : 'a) (sum : real), sum + g x0) 0%r (rm (pick S) S)).
intros a b.
trivial.
save.

(*
lemma map_rm : forall (f:'a->'b) S x, mem x S => (forall y, f y = f x => y = x) => map f (rm x S) = rm (f x) (map f S).
intros f s x h hh.
  apply (Induction.induction_det
(lambda S, S <= s => (
map f (rm x S) = rm (f x) (map f S)
)) _ _ s);first trivial.
simplify.
intros S hyp hyp2.
case (x = pick S);first trivial.
intros neq.
trivial.
trivial.

elimT Induction.induction_det S.
trivial.
simplify.
intros S0 hyp.

delta map.
simplify.
*)

lemma sum_chind :
  forall (f:'a -> real) (g:'a -> 'a) (gg:'a -> 'a) (s:'a set),
    (forall x, g (gg x) = x /\ gg (g x) = x) => (*TROP FORT ?*)
  (sum f s) = sum (lambda x, f (gg x)) (map g s).
proof.
admit.
(*
intros f g gg s bij.
delta sum.
simplify.
rewrite (fold_set_list<:real, 'a> (lambda (x : 'a) (sum : real), sum + f x) 0%r s).
rewrite (fold_set_list<:real, 'a> (lambda (x : 'a) (sum : real), sum + f (gg x)) 0%r (map g s)).
rewrite <- (map_set_list<:'a, 'a> g s).
elimT List.list_ind (set_to_list s);first trivial.
simplify.
intros x xs h.
rewrite (List.map_cons<:'a, 'a> g x xs).
rewrite (List.fold_right_cons<:real, 'a> 0%r (lambda (x0 : 'a) (sum : real), sum + f x0) x xs).
rewrite (List.fold_right_cons<:real, 'a> 0%r (lambda (x0 : 'a) (sum : real), sum + f (gg x0)) (g x) (List.map g xs)).
simplify.
rewrite h.
rewrite (_ : f (gg (g x)) = f x);first trivial.
split.
*)
save.

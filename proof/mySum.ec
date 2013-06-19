require import Set.
require import Real.

require import MySet.

op sum(f:'a -> real, s:'a set) : real =
  List.fold_right (lambda (x:'a, sum:real), sum + f x) (0%r) (enum s).

lemma sum_com : forall f (s t:'a set), s == t => sum f s = sum f t by [].

lemma sum_com2 : forall (f:'a->real) (l1 l2:'a List.list), eq l1 l2 =>
List.fold_right (lambda (x:'a, sum:real), sum + f x) (0%r) l1 =
List.fold_right (lambda (x:'a, sum:real), sum + f x) (0%r) l2
.
(*intros f l1 l2 h.
cut exl1 : (exists (s:'a set), enum s = l1);first (apply (exist l1)).
cut exl2 : (exists (s:'a set), enum s = l2);first (apply (exist l2)).
elim exl1.
elim exl2.
intros s2 h2.
intros s1 h1.
rewrite <- h1.
rewrite <- h2.
apply sum_com.
cut lem : (eq (enum s1) (enum s2)).
smt.
smt.*)
admit.
save.

lemma sum_nil:
  forall (f:'a -> real), sum f Set.empty = 0%r by [].

lemma sum_const : forall (k:real) (f:'a->real) (s:'a set),
  (forall (x:'a), mem x s => f x = k) =>
  sum f s = (card s)%r * k.
admit.
save.

lemma sum_rm :
  forall (f:'a -> real) (s:'a set) (x:'a),
  mem x s =>
  sum f s = (f x) + (sum f (rm x s)).
(*
intros f s x h.
delta sum.
simplify.
rewrite <- (rem_cons<:'a> x (enum s) _).
rewrite <- (List.fold_right_cons<:real, 'a> 0%r (lambda (x0 : 'a) (sum : real), sum + f x0) x (enum s)).
rewrite (enum_rm<:'a> s x).

  apply (Induction.induction
(lambda S, S <> empty => S <= s => (
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S =
f x +
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r (rm x S)
)) _ _ s _);first smt.
simplify.
intros y S h1 h2 h3 h4.
smt.

cut lem : (S <> empty =>
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r S =
f x +
fold_right (lambda (x0 : 'a) (sum : real), sum + f x0) 0%r (rm x S)).

elimT Induction.induction S.
smt.
intros x0 S0 hh hhh hhhh.
smt.
*)
admit.
save.


lemma sum_add :
  forall (f:'a -> real) (s:'a set) (x:'a),
  (!mem x s) =>
  sum f (add x s) = (f x) + (sum f s).
admit.
save.


lemma sum_in :
  forall (f:'a -> real) (s:'a set),
  sum f s = sum (lambda x, if mem x s then f x else 0%r) s.
proof.
admit.
(*
  delta sum.
  simplify.
  intros f s.
  apply (Induction.induction_det
(lambda S, S <= s => (
fold_right (lambda (x : 'a) (sum : real), sum + f x) 0%r S =
fold_right
  (lambda (x : 'a) (sum : real), sum + if mem x s then f x else 0%r) 0%r
  S)
) _ _ s);first smt.
simplify.
intros S h hh.
rewrite (fold_rm<:real,'a> (lambda (x : 'a) (sum : real), sum + f x) 0%r S).
rewrite (fold_rm<:real,'a> (lambda (x : 'a) (sum : real), sum + if mem x s then f x else 0%r) 0%r S).
simplify.
rewrite (h _);first smt.
cut lem : (mem (pick S) s = true);first smt.
rewrite lem.
simplify.
split.
*)
save.

lemma sum_add2 :
  forall (f:'a -> real) (g:'a -> real) (s:'a set),
  (sum f s) + (sum g s) = sum (lambda x, f x + g x) s.
proof.
intros f g s.
delta sum.
elimT Induction.induction_det s;first smt.
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
admit.
save.


op set_to_list(s:'a set) : 'a List.list = fold_right List.(::) (List.__nil) s.

lemma fold_set_list : forall (f:'a -> 'b -> 'b) (e:'b) (s:'a set),
  fold_right f e s = List.fold_right f e (set_to_list s).
intros f e s.
elimT Induction.induction_det s;first smt.
delta set_to_list.
simplify.
intros S h.
rewrite (fold_rm<:'a List.list,'a> List.(::) List.__nil S).
rewrite (fold_rm<:'b,'a> f e S).
rewrite h.
rewrite (List.fold_right_cons<:'b, 'a> e f (pick S) (fold_right List.(::) List.__nil (rm (pick S) S))).
split.
save.

(*
lemma map_set_list : forall (f:'a -> 'b) (s:'a set),
  fold_right f e s = List.map f (set_to_list s).
*)

(*
lemma map_rm : forall (f:'a->'b) S x, mem x S => (forall y, f y = f x => y = x) => map f (rm x S) = rm (f x) (map f S).
intros f s x h hh.
  apply (Induction.induction_det
(lambda S, S <= s => (
map f (rm x S) = rm (f x) (map f S)
)) _ _ s);first smt.
simplify.
intros S hyp hyp2.
case (x = pick S);first smt.
intros neq.
smt.
smt.

elimT Induction.induction_det S.
smt.
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
elimT List.list_ind (set_to_list s);first smt.
simplify.
intros x xs h.
rewrite (List.map_cons<:'a, 'a> g x xs).
rewrite (List.fold_right_cons<:real, 'a> 0%r (lambda (x0 : 'a) (sum : real), sum + f x0) x xs).
rewrite (List.fold_right_cons<:real, 'a> 0%r (lambda (x0 : 'a) (sum : real), sum + f (gg x0)) (g x) (List.map g xs)).
simplify.
rewrite h.
rewrite (_ : f (gg (g x)) = f x);first smt.
split.
*)
save.

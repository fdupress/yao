require import Set.
require import Int.

op integers : int -> int -> int set.
axiom integers_neg : forall (x y:int), x >= y => integers x y = Set.empty.
axiom integers_pos : forall (x y:int), x < y => integers x y = add (y-1) (integers x (y-1)).

lemma integers : forall (x y a:int), (Set.mem a (integers x y)) <=> (x <= a /\ a < y).
  intros x y a.
  case (x < y);last smt.
  rewrite (_ : y = (y-x)+x);first smt.
  intros pos.
  apply (Int.Induction.induction
    (lambda i, mem a (integers x (i+x)) <=> Int.(<=) x a /\ Int.(<) a (i+x))
    _ _ (y-x) _);[smt| |smt].
  simplify.
  intros j h hrec.
  rewrite (integers_pos x (j+x) _);smt.
save.

lemma dec_integers : forall (x y:int),
    x < y =>
    (map (lambda (x : int), x-1) (rm x (integers x y)) =
    (rm (y-1) (integers x y))
    ).
  intros x y h.
  apply Set.extensionality.
  delta Set.(==).
  simplify.
  intros a.
  rewrite (_:rm x (integers x y) = integers (x+1) y);
    first (apply Set.extensionality;delta Set.(==);smt).
  rewrite (_:rm (y-1) (integers x y) = integers x (y-1));
    first (apply Set.extensionality;delta Set.(==);smt).
  apply iff_intro.
  intros hh.
  elim (mem_map_rev<:int,int> (lambda (x0 : int), Int.(-) x0 1) (integers (x+1) y) (a+1) _);
    first (simplify;rewrite (_:(Int.(-) (Int.(+) a 1) 1) = a));smt.
  intros hh.
  rewrite <- (_:(Int.(-) (Int.(+) a 1) 1) = a);first smt.
  apply (mem_map<:int,int> (lambda (x0 : int), Int.(-) x0 1) (integers (x+1) y) (a+1) _).
  smt.
save.

lemma card_integers : forall x y, card (integers x y) = max (y - x) 0.
  intros x y.
  case (x < y);last smt.
  intros h.
  rewrite (_:integers x y=integers x (x+(y-x)));first smt.
  rewrite (_:max (y - x) 0 = y-x);first smt.
  apply (Int.Induction.induction (lambda i, card (integers x (x+i)) = i) _ _ (y-x) _);[smt| |smt].
  simplify.
  intros j hh hrec.
  rewrite (integers_pos x (x+j) _);smt.
save.
require import Array.
require import Int.
require import IntExtra.
require import Pair.
require import Bool.
require import FMap.
require import FSet.
require import NewFMap.
require import Real.
require import List.

require        Sch.
require        SchSec.
require import GarbleTools.
require        SomeGarble.
require        ProjSch.

require import ArrayExt.

import ForLoop.

theory EfficientScheme.  
  clone import ExtWord as W.

  clone SomeGarble.SomeGarble with theory W <- W.

  theory Local.
    (* some types reused for garbling scheme definition  *)
    type 'a tupleGate_t = 'a*'a*'a*'a.
    type tokens_t = (word * word) array.
    type 'a gates_t = ('a tupleGate_t) array.
    type 'a funct_t = topo_t * 'a gates_t.

    (* Semantics of selection is False = fst *)
    op getTok(x:tokens_t) (a:int) (i:bool): word =
      if i then x.[a].`2 else x.[a].`1.

    op evalTupleGate (f:'a tupleGate_t) (x1 x2:bool) =
      let (ff, ft, tf, tt) = f in
      if (!x1) /\ (!x2) then ff else
      if (!x1) /\ ( x2) then ft else
      if ( x1) /\ (!x2) then tf else
      tt.

    (* a b g should be in range 0 .. n + q - 1 to index tokens *)
    op enc (x:tokens_t) (f:bool tupleGate_t) (a b g:int) (x1 x2:bool) : word =
      let xx1 = (getlsb (getTok x a true) = x1) in (* correct token has matching lsb *)
      let xx2 = (getlsb (getTok x b true) = x2) in (* correct token has matching lsb *)
      SomeGarble.DKCSecurity.D.E
        (SomeGarble.Tweak.tweak g x1 x2) (* tweak is calculated with n offset wrt gate number *)
        (getTok x a xx1)
        (getTok x b xx2)
        (getTok x g (evalTupleGate f xx1 xx2)).

    (* a b g should be in range 0 .. n + q - 1 to index tokens *)
    op garbleGate (x:tokens_t) (f:bool tupleGate_t) (a b g:int): word tupleGate_t =
      (enc x f a b g false false,
       enc x f a b g false true,
       enc x f a b g true  false,
       enc x f a b g true  true).

    (* Definitions *)
    op validCircuit(f:(bool funct_t)) =
      let (n, m, q, aa, bb) = f.`1 in
      1 < n /\ 0 < m /\ 0 < q /\ m <= q /\
      size aa = q /\ size bb = q /\ size (snd f) = q /\
      n + q - m = SomeGarble.bound /\
      ForLoop.range 0 q true
        (fun i b,
           b /\ 0 <= aa.[i] /\
           bb.[i] < n + i /\ bb.[i] < n + q - m /\ aa.[i] < bb.[i]).

    pred validCircuitP(f:(bool funct_t)) =
      let (n, m, q, aa, bb) = f.`1 in
      1 < n /\ 0 < m /\ 0 < q /\ m <= q /\
      n + q - m = SomeGarble.bound /\
      size aa = q /\ size bb = q /\ size (snd f) = q /\
      (forall i, 0 <= i < q =>
           0 <= aa.[i] /\
           bb.[i] < n + i /\ bb.[i] < n + q - m /\ aa.[i] < bb.[i]).

    lemma valid_wireinput fn : validCircuit fn <=> validCircuitP fn.
    proof.
      rewrite /validCircuitP /validCircuit.
      elim fn.`1=> n m q aa bb /=.
      (* Put the range call in the correct form for rewriting *)
      cut ->: (fun i b, b /\ 0 <= aa.[i] /\ bb.[i] < n + i /\ bb.[i] < n + q - m /\ aa.[i] < bb.[i])
              = (fun i b, b /\ (fun k,
                                  0 <= aa.[k] /\ bb.[k] < n + k /\
                                  bb.[k] < n + q - m /\ aa.[k] < bb.[k]) i)
        by smt.
      rewrite ForLoop.rangeb_forall. progress. smt. smt. smt. smt. smt. smt. smt. smt.
    qed.

    (** init_dep *)
    (*op init_dep : 'x array -> int -> (int -> 'x array -> 'x) -> 'x array.*)

    op init_dep (xs : 'x array) (l : int) (f : int -> 'x array -> 'x) = 
        let r = offun (fun k, xs.[0]) (size xs + l) in (* creates the space *)
        let r = blit r 0 xs 0 (size xs) in      (* copies the initial value in *)
        ForLoop.range 0 l r (fun i r, r.[i + size xs <- f i r]). (* extends using f *)
    
    lemma init_dep_size (ar:'a array) (l:int) (extract:int -> 'a array -> 'a):
      0 <= l =>
      size (init_dep ar l extract) = (size ar) + l.
    proof.
      move=> hsize.
      rewrite /init_dep.
      pose {2}n := l.
      cut: 0 <= n by smt.
      by elim/intind n;[ |progress;rewrite ForLoop.range_ind_lazy]; smt.
    qed.
    
    (* Will extend whatever input array is there with size = gate count *)
    (* Extract takes the gate count q starting at 0! *)
    op evalComplete (f:'a funct_t) (x:'a array) (extract:'a funct_t -> int -> 'a array -> 'a) : 'a array =
      let (n, m, q, aa, bb) = f.`1 in
      init_dep x q (extract f).

    (* Will extend whatever input array is there with size = gate count, then take outputs *)
    (* Extract takes the _count_ starting at 0! *)
    op evalGen (f:'a funct_t) (x:'a array) (extract:'a funct_t -> int -> 'a array -> 'a) : 'a array =
      let (n, m, q, aa, bb) = f.`1 in
      sub (evalComplete f x extract) (n+q-m) m.

    (* Extraction functions *)
    (* OK to be called from init_dep if size = gate count *)
    op extractB (f:bool funct_t) (g:int) (x:bool array) : bool =
      let (n, m, q, aa, bb) = f.`1 in
      evalTupleGate (snd f).[g] (x.[aa.[g]]) (x.[bb.[g]]).

    (* OK to be called from appendInit if size = gate count *)
    op extractG (ff:word funct_t) (g:int) (x:word array) =
      let (n, m, q, aa, bb) = ff.`1 in
      let a = aa.[g] in
      let b = bb.[g] in
      let aA = x.[a] in
      let bB = x.[b] in
      let a = getlsb aA in
      let b = getlsb bB in
      let t = SomeGarble.Tweak.tweak (n + g) a b in (* tweak takes gate number in 0 range n + q - 1 *)
      SomeGarble.DKCSecurity.D.D t aA bB (evalTupleGate ((snd ff).[g]) a b).

    (* OK to be called from appendInit if size = gate count *)
    op garbMap (x:tokens_t) (f:bool funct_t) (g:int): word tupleGate_t =
      let (n, m, q, aa, bb) = f.`1 in
      garbleGate x (snd f).[g] aa.[g] bb.[g] (n + g).

    (* We define Bellare's preimage sampler Mtopo *)
    op Mtopo (im: topo_t * bool array) : bool funct_t * bool array =
      let (l,y) = im in
      let (n,m,q,A,B) = l in
      let G = offun (fun g,
                   if g  < q - m 
                   then (false,false,false,false) 
                   else let v = y.[g-(q-m)] in (v,v,v,v)) q
                 in
      let fn = ((n,m,q,A,B),G) in 
      let x = offun (fun k, false) n in
      (fn,x).

    (* Makes sure randomness has correct size, so correctness works for all input
       randomness arrays. Security will be associated with concrete randomness generator,
       where size is always of the correct size. *)
    op randFormat(nwires : int, nouts : int, r : tokens_t) : tokens_t =
      if size r < nwires
      then offun (fun k, (setlsb W.zeros false, setlsb W.zeros true))  nwires
      else mapi (fun i (x: word * word),
                   if i < (nwires - nouts)
                   then (setlsb (x.`1) (getlsb (x.`1)), (* to make sure fresh copy *)
                         setlsb (snd x) (!(getlsb (x.`1))))
                   else (setlsb (x.`1) false, setlsb (snd x) true)) r.

    op validInputs (fn:bool funct_t) (i:bool array) = 
      let (n, m, q, aa, bb) = fn.`1 in
      validCircuit fn /\
      n + q <= SomeGarble.maxGates /\
      n = size i.

    (* Evaluates boolean circuit *)
    op eval (fn:bool funct_t) (i:bool array) = evalGen fn i extractB.

    (* Evaluates garbled circuit *)
    op evalG (fn:word funct_t) (i:word array) = evalGen fn i extractG.

    op funG (fn:bool funct_t) (r:tokens_t) =
      let (n, m, q, a, b) = fn.`1 in
      (fn.`1, offun (garbMap r fn) q).

    op inputK (fn:bool funct_t) (r:tokens_t) =
      let (n, m, q, a, b) = fn.`1 in
      sub r 0 n.

    op outputK (fn:bool funct_t) (r:tokens_t) = ().

    op decode (k:unit) (o:word array) = map getlsb o.
  end Local.
  import Local.

  clone import ProjSch.ProjScheme with
    type token_t = word,
    type Sch.Scheme.fun_t = bool funct_t,
    type Sch.Scheme.funG_t = word funct_t,
    type Sch.Scheme.output_t = bool array,
    type Sch.Scheme.outputK_t = unit,
    type Sch.Scheme.outputG_t = word array,
    type Sch.Scheme.leak_t = topo_t,
    type Sch.Scheme.rand_t = (word*word) array,

    pred Sch.Scheme.validRand (fn:fun_t) (x:rand_t) =
      let (n, m, q, aa, bb) = fn.`1 in
      size x = (n + q)%Int,
    op Sch.Scheme.validInputs = validInputs,
    op Sch.Scheme.phi (f:fun_t) = f.`1,
    op Sch.Scheme.eval = eval,
    op Sch.Scheme.evalG = evalG,
    op Sch.Scheme.funG (fn:bool funct_t) (r:tokens_t) = 
      let (n, m, q, aa, bb) = fn.`1 in
      let rf = randFormat (n+q) m r in (* Concrete does not use this op to ensure *)
      funG fn rf,                      (* only one call to randFormat *)
    op Sch.Scheme.inputK(fn : bool funct_t, r : tokens_t) = 
      let (n, m, q, aa, bb) = fn.`1 in
      let rf = randFormat (n+q) m r in (* Concrete does not use this op to ensure *)
      inputK fn rf,                    (* only one call to randFormat *)
    op Sch.Scheme.outputK = outputK,
    op Sch.Scheme.decode = decode,
    op Sch.Scheme.pi_sampler = Mtopo.  

  (*section Tools.*)
  lemma get_rangeMap (x:(word * word) array) (y:int * bool):
    ((ForLoop.range 0 (size x) FMap.empty
      (fun i (gg:(int*bool, word) map),
         gg.[(i, false) <- x.[i].`1].[(i, true) <- snd x.[i]])).[y]) =
           if (0 <= y.`1 < size x)
           then Some ((if snd y then snd else (fun (x:word * word), x.`1)) x.[y.`1])
           else None.
  proof.
    cut: 0 <= size x by smt.
    elim/intind (size x); first smt.
    move=> i hi hr.
    rewrite ForLoop.range_ind_lazy; first smt.
    cut ->: (i + 1 - 1 = i) by smt.
    by rewrite /= !get_set hr; smt.
  qed.

  op mapToArray (x:(int * bool,'a) map): ('a * 'a) array =
    let max = 1 + fold (fun (p:int * bool) (s:int), max (p.`1) s) (-1) (dom x) in
    offun (fun i, (oget x.[(i, false)], oget x.[(i, true)])) max.

  op arrayToMap (x:('a * 'a) array): (int * bool,'a) map = 
    ForLoop.range 0 (size x) FMap.empty
      (fun i (gg:(int * bool,'a) map), gg.[(i, false) <- x.[i].`1].[(i, true) <- snd x.[i]]).
      
  lemma get_arrayToMap (x:('a*'a) array) (y:int*bool):
    (arrayToMap x).[y]
    = if (0 <= y.`1 < size x)
      then Some ((if snd y then snd else (fun (x:'a * 'a), x.`1)) x.[y.`1])
      else None.
  proof.
    rewrite /arrayToMap /=.
    cut: 0 <= size x by smt.
    elim/intind (size x); first by smt.
    move=> i hi hr.
    rewrite ForLoop.range_ind_lazy; first smt.
    cut ->: (i + 1 - 1 = i) by smt.
    by rewrite /= !get_set hr; smt.
  qed.

  lemma mem_dom_arrayToMap (x:('a*'a) array) b i:
    (0 <= i < size x) <=> mem (dom (arrayToMap x)) (i, b).
  proof.
    rewrite /arrayToMap /= mem_dom.
    elim/array_ind_snoc x; first smt.
    move=> x0 xs h.
    rewrite ForLoop.range_ind_lazy //= 1:smt !get_set !size_snoc.
    case (i = size xs).
      by move=> -> /=; case b; smt.
    move=> hlen.
    cut -> /=: size xs + 1 - 1 = size xs by smt.
    cut:= hlen; rewrite eq_sym -neqF=> -> /=.
    rewrite //= -ForLoop.range_restr 1:smt.
    cut ->: (fun (k : int) (a : (int * bool, 'a) map),
               if 0 <= k < size xs then
                 (fun (i0 : int) (gg : (int * bool, 'a) map),
                    gg.[(i0, false) <- (xs ::: x0).[i0].`1].[(i0, true) <-
                      snd (xs ::: x0).[i0]]) k a
               else a) =
            (fun (k : int) (a : (int * bool, 'a) map),
               if 0 <= k < size xs then
                 (fun (i0 : int) (gg : (int * bool, 'a) map),
                    gg.[(i0, false) <- xs.[i0].`1].[(i0, true) <-
                      snd xs.[i0]]) k a
               else a).
      apply ExtEq.fun_ext=> k /=.
      apply ExtEq.fun_ext=> a /=.
      case (0 <= k < size xs)=> hk; last smt.
      by rewrite get_snoc; smt.
    by rewrite ForLoop.range_restr 1:smt; smt.
  qed.

  op interval : int -> int -> int fset.
  axiom interval_neg : forall (x y:int), y < x => interval x y = fset0.
  axiom interval_pos : forall (x y:int), x <= y => interval x y = (fset1 y) `|` (interval x (y-1)).

  lemma mem_interval : forall (x y a:int), (mem (interval x y) a) <=> (x <= a /\ a <= y).
    proof.
      move => x y a.
      case (x <= y)=> h; last first.
        by rewrite interval_neg; smt.
      rewrite (_ : y = (y-x+1)-1+x);first smt.
      apply (intind
      (fun i, mem (interval x ((i-1)+x)) a <=> Int.(<=) x a /\ Int.(<=) a ((i-1)+x))).
        split; rewrite interval_neg; smt.
        simplify.
        move => j hh hrec.
        rewrite interval_pos;first smt.
        rewrite in_fsetU. simplify. smt. smt. 
  qed.

  (** rm *)
  (*op rm ['a] (s : 'a fset) (x : 'a) = oflist (rem x (elems s)).*)

  (*lemma mem_rm_eq: forall (x:'a) (X:'a fset),
      !(mem (rm X x) x).
      proof.
      move => x X.
      rewrite /rm.
      rewrite mem_oflist.
      smt.
    qed.*)

  (*lemma mem_rm_neq: forall (x x':'a) (X:'a fset),
    x <> x' => mem (rm X x') x = mem X x. 
      proof.
      move => x x' X.
      elim /fset_ind X.
        smt.
      move => x0 s Hmemsx0 Hind Hdiff.
        rewrite /rm.
        rewrite mem_oflist.
        rewrite in_fsetU. rewrite -Hind. exact Hdiff.
        rewrite /rm. rewrite mem_oflist. 
        cut Heqor: forall a b c, a => a = (b \/ c) <=> (a = b \/ a = c) by smt.
        apply Heqor.
        cut ->: mem (rem x' (elems (s `|` fset1 x0))) x = mem (rm (s `|` fset1 x0) x') x by smt.
        rewrite mem_rm_eq.
        admit. smt.
        smt.
        cut -> : mem (rem x' (elems (s `|` fset1 x0))) x = (mem (rem x' (elems s)) x \/ mem (fset1 x0) x) <=> mem (rem x' (elems (s `|` fset1 x0))) x = (mem (rem x' (elems s)) x) \/ mem (rem x' (elems (s `|` fset1 x0))) x = (mem (fset1 x0) x) by smt.
        rewrite (perm_eq_mem (rem x' (elems (s `|` fset1 x0))) (elems (s `|` fset1 x0))).
        rewrite perm_eq_refl_eq.
        cut ->: elems (s `|` fset1 x0) = elems (oflist (elems s ++ [x0])) by smt.
        smt.
        admit. trivial. reflexivity.
    qed.

        move : Hdiff. move : Hind. move : x'.
      cut ->: forall (x' : 'a), mem (rem x' (elems (s `|` fset1 x0))) x = mem (elems (s `|` fset1 x0)) x by smt.
    qed.
*)
      
  (*  lemma mem_rm: forall (x x':'a) (X:'a fset),
    mem (rm X x') x = (mem X x /\ x' <> x).
    proof.
      intros ? ? ?.
    case (x'=x)=> ?.
    rewrite H.
    cut -> : mem (rm X x) x = false;first apply neqF;apply mem_rm_eq.
    by trivial.
    simplify.
    apply mem_rm_neq. cut ->: ! (x = x') <=> ! (x' = x) by smt. exact H.
  qed.*)

(*lemma mem_rm1: forall (x x':'a) (X:'a fset),
    mem (rm X x') x => mem X x by [].
  lemma mem_rm2: forall (x x':'a) (X:'a fset),
      mem (rm X x') x => x <> x' by [].
    lemma rm_nin_id: forall (x:'a) (X:'a fset),
        !(mem X x) => X = rm X x
        by (intros=> x X x_nin_X; apply fsetP; smt).
      lemma rm_rmE : forall x y (xs:'a fset), rm (rm xs y) x = rm (rm xs x) y.
          proof strict.
          intros=> x y xs.
          apply fsetP=> a.
            rewrite ! mem_rm ! andA (andC (! y = a)) //.
       qed.

        
     lemma elems_rm: forall (x:'a) (X:'a fset),
         elems (rm X x) = rem x (elems X). proof. admit. qed.
         
lemma rm_leq: forall (x:'a) (X:'a fset), rm X x <= X by [].*)
(*lemma rm_add_eq: forall (x:'a) X,
  rm x (add x X) = rm x X.
proof strict.
intros=> x X; apply fset_ext=> x';
rewrite 2!mem_rm mem_add orDand (rw_eq_sym x' x);
cut ->: (x = x' /\ !x = x') = false; first by case (x = x')=> h /= //.
by trivial.
qed.
lemma rm_add_neq: forall (x x':'a) X,
  x <> x' => rm x (add x' X) = add x' (rm x X).
proof strict.
intros=> x x' X x_x'; apply fset_ext;
delta (==); beta=> x0;
case (x = x0)=> x_x0.
  by subst x0; smt.
  by rewrite mem_rm_neq; smt.
qed.
lemma add_rm_in: forall (x:'a) (X:'a fset),
  mem x X => add x (rm x X) = X.
proof strict.
intros=> x X x_in_X; apply fset_ext; apply perm_eq;
apply (perm_trans (x::(elems (rm x X)))); first apply elems_add_nin; apply mem_rm_eq.
apply (perm_trans (x::(rm x (elems X)))); first apply perm_cons; apply elems_rm.
smt.
qed.
lemma add_destruct: forall (x:'a) (X:'a fset),
  (exists (X':'a fset), !mem x X' /\ X = add x X') <=> mem x X
by [].*)
  
  (*lemma dec_interval : forall (x y:int),
	    x <= y =>
	    (image (fun (x : int), x-1) (rm (interval x y) x) =
	    (rm (interval x y) y)
	  ).
          proof.
	  intros x y h.
	  apply fsetP=> a.
	  rewrite imageP.
	  rewrite ! mem_rm ! mem_interval.
	  split.
	  intros=> /= [x0] [h1].
	  subst.
	  smt.
	  intros=> hh.
	  exists (a+1).
	  simplify.
	  rewrite ! mem_rm ! mem_interval.
smt.
          qed.*)
          
  lemma card_interval_max : forall x y, card (interval x y) = max (y - x + 1) 0.
  proof.
    move => x y.
    case (x <= y); last first.
      move => Hxy. rewrite interval_neg. smt. smt.
    move => h.
    rewrite (_:interval x y=interval x (x+(y-x+1)-1));first smt.
    rewrite (_:max (y - x + 1) 0 = y-x+1);first smt.
    apply (intind (fun i, card (interval x (x+i-1)) = i)).
    simplify. rewrite interval_neg. smt. smt. 
    simplify.
    move => j hh hrec.
    rewrite interval_pos; first by smt.
    rewrite fcardUI_indep. smt. smt. smt. 
qed.
  
  lemma dom_arrayToMap (x:('a * 'a) array):
    dom (arrayToMap x) =
      FSet.( `|` ) (image (fun i, (i,false)) (interval 0 (size x - 1)))
            (image (fun i, (i, true)) (interval 0 (size x - 1))).
  proof.
    apply fsetP=> y.
    elim y=> i b.
    rewrite -mem_dom_arrayToMap in_fsetU; split.
      move=> h; case b=> hb; [right | left];
         cut ->: forall (b:bool), (i, b) = (fun (i0 : int), (i0, b)) i by smt;
         apply imageP; rewrite mem_interval; smt. smt. smt.
      rewrite !imageP. progress. smt. smt. 
  qed.
  
  lemma max_arrayToMap (x:('a * 'a) array):
    1 + fold (fun (p:int * bool) (s:int),
                max (p.`1) s) (-1) (dom (arrayToMap x)) =
      size x.
  proof.
    rewrite dom_arrayToMap.
    pose xs:= FSet.(`|`) _ _.
    cut Antisymm: forall (x y : int), x <= y => y <= x => x = y by smt.
    apply Antisymm.
      cut: forall y, mem xs y => y.`1 < size x.
         by move=> y; rewrite /xs  !in_fsetU=> h; smt.
    elim/fset_ind xs. smt. progress. rewrite (foldC (x0) _ _ _). smt. smt.
    cut ->: (s `|` fset1 x0) `\` fset1 x0 = s by smt. simplify. smt.
    case (size x = 0)=> h. 
    cut ->: fold (fun (p : int * bool) (s : int) => max p.`1 s) (-1) xs = List.foldr (fun (p : int * bool) (s : int) => max p.`1 s) (-1) (elems xs) by smt.
    simplify. smt.
    cut: mem xs ((size x - 1), false).
        by rewrite /xs in_fsetU !imageP; left; exists (size x - 1); smt.
    elim/fset_ind xs. progress. smt. progress.
    rewrite (foldC x0 _ _ _). progress. smt. smt.
    simplify.
    cut ->: ((s `|` fset1 x0) `\` fset1 x0) = s by smt.
    smt.
  qed.

  lemma size_arrayToMap (x:('a * 'a) array) n:
    0 <= n =>
    (forall i b, (0 <= i < n) <=> mem (dom (arrayToMap x)) (i, b)) =>
    size x = n.
  proof.
    rewrite dom_arrayToMap=> npos.
    move: npos x.
    elim/intind n=> //.
      move=> x h.
      cut:= h 0 false=> /=.
      rewrite in_fsetU !imageP -nor.
      move=> [i_false i_true].
      cut: !mem (interval 0 (size x - 1)) 0 by smt.
      rewrite mem_interval.
      smt.

      move=> i le0i IH x IH1.
      cut ineg: i + 1 <= size x.
        cut:= IH1 i false=> /=.
        rewrite in_fsetU !imageP.
        cut: 0 <= i < i + 1 = true by smt.
        move=> i_bnd. rewrite i_bnd. 
        by smt.
      case (i + 1 < size x)=> hi0; last smt.
      cut hh: mem (FSet.(`|`)
                  (image (fun (i1 : int), (i1, false))
                     ((interval 0 (size x - 1))))
                  (image (fun (i1 : int), (i1, true))
                     ((interval 0 (size x - 1))))) (i+1, false)
        by smt.
      cut: 0 <= i + 1 < i + 1 by smt.
      smt.
  qed.

  lemma map_array (x:(int*bool, 'a) map) :
    (let max = 1 + fold (fun (p : int * bool) (s : int), max (p.`1) s) (-1) (dom x) in
     forall (y:int * bool), (mem (dom x) (y.`1,  true) <=> 0 <= y.`1 < max) /\
                            (mem (dom x) (y.`1, false) <=> 0 <= y.`1 < max) /\ 0 <= max) =>
    arrayToMap (mapToArray x) = x.
  proof.
    rewrite /mapToArray /=.
    pose max:= 1 + fold (fun (p : int * bool) (s : int), max (p.`1) s) (-1) (dom x).
    move=> h.
    apply map_ext=> y.
    rewrite get_arrayToMap size_offun. 
    case (0 <= y.`1 < max)=> hy.
      rewrite !offunE //.
      elim y hy=> y1 y2; rewrite /snd /= => hy /=.
      rewrite !/snd /=.
      move: (h (y1,y2))=> /=; rewrite hy !mem_dom /=.
      case y2=> y2_v.
        by smt. 
        by smt. 
      move: hy (h y); rewrite -neqF !mem_dom (*(eq_sym None)*)=> -> /=.
      elim y=> y1 y2 /=; case y2. smt. smt.
  qed.

  lemma array_map (x:('a * 'a) array): mapToArray(arrayToMap x) = x.
  proof.
    rewrite /mapToArray /=.
    apply arrayP; split; first by rewrite size_offun; smt.
    rewrite size_offun.
    rewrite max_arrayToMap.
    move=> i hi.
    rewrite offunE //=; first by smt.
    rewrite !get_arrayToMap !/snd /=. 
    by smt.
  qed.

  op init_gates (size:int) (f:int->bool->bool->'a) : 'a gates_t =
    offun (fun (g:int), (f g false false, f g false true, f g true false, f g true true)) size.

  op arrayToMap2 (n q:int) (x:('a*'a*'a*'a) array) =
    if size x = q then
      SomeGarble.init_gates n q (fun g a b, evalTupleGate x.[g-n] a b)
    else
      FMap.empty.

  op mapToArray2 (n q:int) (x:(int*bool*bool, 'a) map) = init_gates q (fun g a b, oget x.[(g+n, a, b)]).
  
  lemma appendInit_init_dep (ar:'a array) (l:int) (extract1 extract2:int -> 'a array -> 'a):
    0 <= l =>
    let n = size ar in
    (forall (i:int) (xs1 xs2:'a array), 0 <= i < l =>
      (forall k, 0 <= k < i + n => xs1.[k] = xs2.[k]) =>
      extract1 (n+i-1) xs1 = extract2 i xs2) =>
    appendInit ar l extract1 = init_dep ar l extract2.
  proof.
    move=> hsize.
    progress.
    cut: size (init_dep ar l extract2) = (size ar) + l /\
         (forall k, 0 <= k < size ar + l =>
            (appendInit ar l extract1).[k] = (init_dep ar l extract2).[k]).
      rewrite /appendInit /= /init_dep /=.
      pose {1 4 5 6}n:= l.
      cut: n <= l by trivial.
      cut: 0 <= n by trivial.
      elim/intind n=> //.
        by progress; smt.
        move => i Hi IH Hi1; split.
          by rewrite ForLoop.range_ind_lazy; smt.

        progress.
          rewrite ForLoop.range_ind_lazy; first smt.
          rewrite (ForLoop.range_ind_lazy 0); first smt.
          cut:= appendInit_size ar i extract1.
          simplify appendInit appender=> appLen.
          move: (appLen _) => // {appLen} appLen.
          cut-> : forall x, x + (i + 1) - 1 = x + i by smt.
          cut-> : i + 1 - 1 = i by smt.
          rewrite get_snoc; first by smt. 
          rewrite get_set; first smt.
          rewrite appLen //.
          cut:= IH _; first smt.
          move => [H11 H12].
          case (k < size ar + i)=> h.
            cut Hisize : (i + size ar = k) = false by smt.
            simplify.
            rewrite -H12; first smt.
             simplify appender; smt.
            cut Hisize : (i + size ar = k) = true by smt.
            simplify.
              cut ->:
          (if k = i + size ar then
  extract2 i
    (range 0 i
       (blit (offun (fun (_ : int) => ar.[0]) (size ar + l)) 0 ar 0 (size ar))
       (fun (i0 : int) (r : 'a array) => r.[i0 + size ar <- extract2 i0 r]))
else
  (range 0 i
     (blit (offun (fun (_ : int) => ar.[0]) (size ar + l)) 0 ar 0 (size ar))
     (fun (i0 : int) (r : 'a array) => r.[i0 + size ar <- extract2 i0 r])).[k]) = extract2 i
    (range 0 i
       (blit (offun (fun (_ : int) => ar.[0]) (size ar + l)) 0 ar 0 (size ar))
       (fun (i0 : int) (r : 'a array) => r.[i0 + size ar <- extract2 i0 r])) by  smt.
            apply H; first smt.
            progress.
            rewrite -H12; first smt.
            by simplify appender.
        move => h.
        by apply arrayP; smt.
  qed.
  
  lemma map_array2 (n q:int) (x:(int * bool * bool,'a) map):
    0 <= q =>
    (forall (g:int) a b, x.[(g, a, b)] <> None <=> n <= g < n + q) =>
    arrayToMap2 n q (mapToArray2 n q x) = x.
  proof.
    rewrite /arrayToMap2 /mapToArray2=> hq h.
    apply map_ext=> y.
    elim y=> g a b. 
    cut:= SomeGarble.get_initGates n q (fun (g : int) (a b : bool),
            evalTupleGate (init_gates q
              (fun (g1 : int) (a1 b1 : bool), oget x.[(g1+n, a1, b1)])).[g-n]
              a b)
            g a b _=> //.
    rewrite !/snd.
    cut -> : size
          (init_gates q
             (fun (g0 : int) (a0 b0 : bool), oget (x.[(g0 + n, a0, b0)]))) =
        q by smt=> /= ->.
    case (n <= g < n + q)=> hc; last smt.
    simplify init_gates.
    rewrite offunE; first smt.
    simplify evalTupleGate.
    rewrite (_: g - n + n = g); first by smt. progress. smt.
  qed.

  lemma array_map2 (n q:int) (x:('a * 'a * 'a * 'a) array):
    size x = q =>
    mapToArray2 n q (arrayToMap2 n q x) = x.
  proof.
    rewrite /arrayToMap2 /mapToArray2 /snd=> hq.
    apply arrayP.
    simplify init_gates; split; first smt.
    rewrite size_offun. 
    move=> i ih.
    rewrite offunE /= //; first by smt.
    rewrite hq /= !SomeGarble.get_initGates; first 4 smt.
    cut ->: (n <= i + n < n + q) = true; first smt.
    by rewrite /evalTupleGate; smt.
  qed.

  lemma size_randFormat nq m r: nq = Array.size r => size (randFormat nq m r) = size r.
  proof. by progress; rewrite /randFormat /= size_mapi. qed.
  (*end section Tools.*)
    
  (*section Bijection*)
  pred functD_topo_valid (x:topo_t) = let (n, m, q, aa, bb) = x in
    0 <= n /\ 0 <= q /\
    size aa = (n + q)%Int /\
    size bb = (n + q)%Int /\
    (forall (i:int), 0 <= i < n => (aa.[i])%Array = 0 /\ (bb.[i])%Array = 0).

  pred functE_topo_valid (x:topo_t) =  let (n, m, q, aa, bb) = x in
    0 <= n /\ 0 <= q /\
    size aa = q /\
    size bb = q.

  op topoED(x:topo_t) : topo_t =
    let (n, m, q, aa, bb) = x in
    (n, m, q, (offun (fun i, 0) n) || aa, (offun (fun i, 0) n) || bb).

  op topoDE(x:topo_t) : topo_t =
    let (n, m, q, aa, bb) = x in
    (n, m, q, sub aa n q, sub bb n q).

  lemma topo_EDDE x: functD_topo_valid x =>
      topoED (topoDE x) = x.
  proof strict.
    elim x=> n m q aa bb Htopo. 
    progress; apply arrayP; split; first by smt.
    move=> i; rewrite size_append // size_offun ?size_sub; first 3 by smt.
    by move => i_bnd; case (i < n); move => H; rewrite /functD_topo_valid /=; progress;
       [rewrite get_append_left | rewrite get_append_right]; smt. 
    smt.
    move => i; rewrite size_append // size_offun ?size_sub; first 3 smt.
    by move => i_bnd; case (i < n); move => H; rewrite /functD_topo_valid /=; progress;
       [rewrite get_append_left | rewrite get_append_right]; smt.
  qed.

  lemma topo_DEED x: functE_topo_valid x =>
    topoDE (topoED x) = x. 
  proof.
    simplify functE_topo_valid; elim x => n m q aa bb /=. 
    progress.
    apply arrayP; split; first by smt.
    by move => i i_bound; smt.
    apply arrayP; split; first by smt.
    by move => i i_bound; smt.
  qed.
      
  op leakED (x:ProjScheme.Sch.Scheme.leak_t): SomeGarble.GSch.Sch.Scheme.leak_t = topoED x.
  op leakDE (x:SomeGarble.GSch.Sch.Scheme.leak_t): ProjScheme.Sch.Scheme.leak_t = topoDE x.

  lemma leak_EDDE x: functD_topo_valid x =>
      leakED (leakDE x) = x by smt.

  lemma leak_DEED x: functE_topo_valid x =>
    leakDE (leakED x) = x by smt.

  op inputED (x:ProjScheme.Sch.Scheme.Input.input_t): SomeGarble.GSch.Sch.Scheme.Input.input_t = x.
  op inputDE (x:SomeGarble.GSch.Sch.Scheme.Input.input_t): ProjScheme.Sch.Scheme.Input.input_t = x.

  lemma input_EDDE x: inputED (inputDE x) = x by delta.

  lemma input_DEED x: inputDE (inputED x) = x by delta.

  op outputED (x:ProjScheme.Sch.Scheme.output_t): SomeGarble.GSch.Sch.Scheme.output_t = x.
  op outputDE (x:SomeGarble.GSch.Sch.Scheme.output_t): ProjScheme.Sch.Scheme.output_t = x.

  lemma output_EDDE x: outputED (outputDE x) = x by delta.

  lemma output_DEED x: outputDE (outputED x) = x by delta.

  op outputKED (x:ProjScheme.Sch.Scheme.outputK_t): SomeGarble.GSch.Sch.Scheme.outputK_t = x.
  op outputKDE (x:SomeGarble.GSch.Sch.Scheme.outputK_t): ProjScheme.Sch.Scheme.outputK_t = x.

  lemma outputK_EDDE x: outputKED (outputKDE x) = x by delta.

  lemma outputK_DEED x: outputKDE (outputKED x) = x by delta.

  op outputGED (x:ProjScheme.Sch.Scheme.outputG_t): SomeGarble.GSch.Sch.Scheme.outputG_t = x.
  op outputGDE (x:SomeGarble.GSch.Sch.Scheme.outputG_t): ProjScheme.Sch.Scheme.outputG_t = x.

  lemma outputG_EDDE x: outputGED (outputGDE x) = x by delta.

  lemma outputG_DEED x: outputGDE (outputGED x) = x by delta.

  op inputGED (x:ProjScheme.Sch.Scheme.Input.inputG_t): SomeGarble.GSch.Sch.Scheme.Input.inputG_t = x.
  op inputGDE (x:SomeGarble.GSch.Sch.Scheme.Input.inputG_t): ProjScheme.Sch.Scheme.Input.inputG_t = x.

  lemma inputG_EDDE x: inputGED (inputGDE x) = x by delta.

  lemma inputG_DEED x: inputGDE (inputGED x) = x by delta.

  op inputKED (x:ProjScheme.Sch.Scheme.Input.inputK_t): SomeGarble.GSch.Sch.Scheme.Input.inputK_t =
    arrayToMap x.
  op inputKDE (x:SomeGarble.GSch.Sch.Scheme.Input.inputK_t): ProjScheme.Sch.Scheme.Input.inputK_t =
    mapToArray x.

  pred tokensD_valid (x:SomeGarble.tokens_t) =
    (let max = 1 + fold (fun (p : int * bool) (s : int), max (p.`1) s) (-1) (dom x) in
     forall (y:int*bool), (mem (dom x) (y.`1, true) <=> 0 <= y.`1 < max) /\
                         (mem (dom x) (y.`1, false) <=> 0 <= y.`1 < max) /\ 0 <= max).

  lemma inputK_EDDE x: tokensD_valid x => inputKED (inputKDE x) = x by smt. 
  lemma inputK_DEED x: inputKDE (inputKED x) = x by smt.

  op randED (x:ProjScheme.Sch.Scheme.rand_t): SomeGarble.GSch.Sch.Scheme.rand_t = arrayToMap x.
  op randDE (x:SomeGarble.GSch.Sch.Scheme.rand_t): ProjScheme.Sch.Scheme.rand_t = mapToArray x.

  lemma rand_EDDE x: tokensD_valid x => randED (randDE x) = x by smt.
  lemma rand_DEED x: randDE (randED x) = x by smt.

  op funED (x:ProjScheme.Sch.Scheme.fun_t): SomeGarble.GSch.Sch.Scheme.fun_t =
    let (n, m, q, aa, bb) = x.`1 in (topoED (x.`1), arrayToMap2 n q (snd x)).
  op funDE (x:SomeGarble.GSch.Sch.Scheme.fun_t): ProjScheme.Sch.Scheme.fun_t =
    let (n, m, q, aa, bb) = x.`1 in (topoDE (x.`1), mapToArray2 n q (snd x)).

  pred functD_gg_valid (x:'a SomeGarble.funct_t) = let (n, m, q, aa, bb) = x.`1 in
    (forall (g:int) a b, (snd x).[(g, a, b)] <> None <=> n <= g < n + q).

  pred functE_gg_valid (x:'a funct_t) =  let (n, m, q, aa, bb) = x.`1 in
    size (snd x) = q.

  pred functD_valid (x:'a SomeGarble.funct_t) = functD_topo_valid (x.`1) /\ functD_gg_valid x.

  pred functE_valid (x:'a funct_t) = functE_topo_valid (x.`1) /\ functE_gg_valid x.

  lemma fun_EDDE x : functD_valid x => funED (funDE x) = x.
  proof.
    simplify funED funDE functD_valid functD_topo_valid functD_gg_valid.
    elim x=> topo gg /=.
    elim topo=> n m q aa bb /=.
    rewrite !/snd /=.
    progress.
      apply arrayP; split.
        smt.
        move=> i; rewrite size_append // size_offun ?size_sub; first 3 smt.
        by move=> i_bnd; case (i < n)=> i_n; [rewrite get_append_left | rewrite get_append_right]; smt.
      apply arrayP; split.
        smt.
        move=> i; rewrite size_append // size_offun ?size_sub; first 3 smt.
        by move=> i_bnd; case (i < n)=> i_n; [rewrite get_append_left | rewrite get_append_right]; smt.
      smt.
  qed.

  lemma fun_DEED x : functE_valid x => funDE (funED x) = x.
  proof.
    rewrite /funED /funDE /functE_valid /functE_topo_valid /functE_gg_valid /=.
    elim x=> topo gg /=.
    elim topo=> n m q aa bb /=.
    by rewrite !/snd; smt.
  qed.

  op funGED (x:ProjScheme.Sch.Scheme.funG_t) : SomeGarble.GSch.Sch.Scheme.funG_t =
    let (n, m, q, aa, bb) = x.`1 in
    (topoED (x.`1), arrayToMap2 n q (snd x)).
  op funGDE (x:SomeGarble.GSch.Sch.Scheme.funG_t) : ProjScheme.Sch.Scheme.funG_t =
    let (n, m, q, aa, bb) = x.`1 in
    (topoDE (x.`1), mapToArray2 n q (snd x)).

  lemma funG_EDDE x : functD_valid x => funGED (funGDE x) = x.
  proof.
    rewrite /funGED /funGDE /functD_valid /functD_topo_valid /functD_gg_valid /=.
    elim x=> topo gg /=.
    elim topo=> n m q aa bb /=.
    rewrite !/snd /=.
    progress.
      apply arrayP; split.
        smt.
        move=> i; rewrite size_append // size_offun ?size_sub; first 3 smt.
        by move=> i_bnd; case (i < n)=> i_n; [rewrite get_append_left | rewrite get_append_right]; smt.
      apply arrayP; split.
        smt.
        move=> i; rewrite size_append // size_offun ?size_sub; first 3 smt.
        by move=> i_bnd; case (i < n)=> i_n; [rewrite get_append_left | rewrite get_append_right]; smt.
      smt.
  qed.

  lemma funG_DEED x : functE_valid x => funGDE (funGED x) = x.
  proof.
    rewrite /funGED /funGDE /functE_valid /functE_topo_valid /functE_gg_valid.
    elim x=> topo gg /=.
    elim topo=> n m q aa bb /=.
    by rewrite /snd; smt.
  qed.
  (*end section Bijection*)

  (* Begin morphism *)
  pred encode_valid (k:SomeGarble.GSch.Sch.Scheme.Input.inputK_t) (i:SomeGarble.GSch.Sch.Scheme.Input.input_t) = 1 + fold (fun (p:int * bool) (s:int), max (p.`1) s) (-1) (dom k) = size i.

  lemma encode_ED (k:SomeGarble.GSch.Sch.Scheme.Input.inputK_t) (i:SomeGarble.GSch.Sch.Scheme.Input.input_t) :
    encode_valid k i =>
    inputGED (ProjScheme.Sch.Scheme.Input.encode (inputKDE k) (inputDE i)) =
     SomeGarble.GSch.Sch.Scheme.Input.encode k i.
  proof.
    simplify inputGED ProjScheme.Sch.Scheme.Input.encode inputKDE inputDE
             SomeGarble.GSch.Sch.Scheme.Input.encode
             SomeGarble.GSch.Sch.Scheme.Input.encode
             mapToArray encode_valid.
    pose max:= 1 + fold (fun (p:int * bool) (s:int), max (p.`1) s) (-1) (dom k).
    move=> hmax.
    cut hli: 0 <= size i by apply Array.size_ge0.
    subst.
    apply arrayP.
    split; first by rewrite !size_offun //; smt.
    rewrite ?size_offun //.
    move => j hj.
    rewrite !offunE //=; first 2 by smt.
    rewrite !offunE //=; first 2 by smt.
  qed.

  lemma phi_ED (fn:bool SomeGarble.funct_t) : functD_topo_valid (fn.`1) =>
    leakED (ProjScheme.Sch.Scheme.phi (funDE fn)) = SomeGarble.GSch.Sch.Scheme.phi fn.
  proof.
    simplify delta.
    elim fn=> topo gg /=.
    elim topo=> n m q aa bb /=.
    progress; apply arrayP; split.
      smt.
      move=> i; rewrite size_append // size_offun ?size_sub; first 3 smt.
      by move=> i_bnd; case (i < n)=> i_n; [rewrite get_append_left | rewrite get_append_right]; smt.
      smt.
      move=> i; rewrite size_append // size_offun ?size_sub; first 3 smt.
      by move=> i_bnd; case (i < n)=> i_n; [rewrite get_append_left | rewrite get_append_right]; smt.
  qed.

  pred eval_valid (fn:'a SomeGarble.funct_t) (i:'a array) =
    let (n, m, q, aa, bb) = fn.`1 in
    0 <= q /\ size aa = n + q /\ size bb = n + q /\ size i = n /\
    (forall i0, 0 <= i0 < q => 0 <= aa.[i0 + n] < i0 + n) /\
    (forall i0, 0 <= i0 < q => 0 <= bb.[i0 + n] < i0 + n).

  lemma eval_ED fn i : eval_valid fn i =>
    outputED (ProjScheme.Sch.Scheme.eval (funDE fn) (inputDE i)) = SomeGarble.GSch.Sch.Scheme.eval fn i.
  proof.
    simplify outputED ProjScheme.Sch.Scheme.eval funDE inputDE SomeGarble.GSch.Sch.Scheme.eval
             evalTupleGate SomeGarble.GSch.Sch.Scheme.eval init_gates fst snd evalComplete extract mapToArray2
             eval evalGen topoDE topoED eval_valid.
    elim fn=> topo gg /=.
    elim topo=> n m q aa bb /=.
    move => hvalid; elim hvalid => hq hvalid; elim hvalid => haa hvalid; elim hvalid => hbb hvalid; elim hvalid => hi hvalid; elim hvalid => haa2 hbb2.
    congr=> //.
    simplify GarbleTools.evalComplete.
    apply eq_sym.
    apply appendInit_init_dep; first smt.
    progress.
    rewrite /extractB snd_pair /= /evalTupleGate offunE. smt. simplify.
    rewrite hi.
    cut ->: gg.[(n + i0 - 1 + 1, xs1.[aa.[n + i0 - 1 + 1]], xs1.[bb.[n + i0 - 1 + 1]])] = gg.[(n + i0, xs1.[aa.[n + i0]], xs1.[bb.[n + i0]])] by smt.
    case (xs2.[(sub aa n q).[i0]]).
    case (xs2.[(sub bb n q).[i0]]).
    move => Hc1 Hc2.
    simplify. smt.
    move => Hc1 Hc2.
    simplify. smt.
    case (xs2.[(sub bb n q).[i0]]).
    move => Hc1 Hc2. simplify. smt.
    move => Hc1 Hc2. simplify. smt.
  qed.
  
  lemma evalG_ED fn i : eval_valid fn i =>
    outputGED (ProjScheme.Sch.Scheme.evalG (funGDE fn) (inputGDE i)) = SomeGarble.GSch.Sch.Scheme.evalG fn i.
  proof.
    simplify outputGED ProjScheme.Sch.Scheme.evalG funGDE inputGDE SomeGarble.GSch.Sch.Scheme.evalG
             evalTupleGate SomeGarble.GSch.Sch.Scheme.evalG init_gates fst snd evalComplete extract mapToArray2
             evalG evalGen topoDE topoED eval_valid.
    elim fn=> topo gg hx /=.
    elim topo hx=> n m q aa bb /=.
    progress.
    congr=> //.
    simplify GarbleTools.evalComplete.
    apply eq_sym.
    apply appendInit_init_dep; first smt.
    progress.
    rewrite /extractG snd_pair /= /evalTupleGate offunE ?hli; first smt.
    cut -> : size i + i0 - 1 + 1 = size i + i0 by smt.
    rewrite !H6; first 2 smt.
    congr; first 3 smt.
    
    rewrite !get_sub; first 8 smt.
    smt.
  qed.

  pred funG_valid (fn:'a SomeGarble.funct_t) (r:(int*bool, word) map) =
    functD_topo_valid (fn.`1) /\
    let (n,m,q,aa,bb) = fn.`1 in 
    1 + fold (fun (p:int * bool) (s:int), max (p.`1) s) (-1) (dom r) = (n + q)%Int /\
    forall (i:int), n <= i < n + q =>
      0 <= (aa.[i])%Array < n + q /\
      0 <= (bb.[i])%Array < n + q.

  op randFormatD (t:topo_t) (r:SomeGarble.GSch.Sch.Scheme.rand_t) = 
    let (n, m, q, aa, bb) = t in
    randED (randFormat (n+q)%Int m (randDE r)).

  pred validRandD (x:'a funct_t) (r:(word * word) array) =
    let (n,m,q,aa,bb) = x.`1 in
    0 <= (n + q)%Int /\
    size r = n + q.

  lemma validRand_DE fn i:
    validRandD fn i =>
    ProjScheme.Sch.Scheme.validRand fn i =
     SomeGarble.GSch.Sch.Scheme.validRand (funED fn) (randFormatD (funED fn).`1 (randED i)).
  proof.
    elim fn=> t gg /=.
    elim t=> n m q aa bb /=.
    simplify validRandD.
    move=> vRand.
    rewrite /Sch.Scheme.validRand /=.
    cut leni_nq: size i = n + q by smt. 
    rewrite /funED snd_pair /=.
    rewrite /topoED /=.
    rewrite /randFormatD /=.
    rewrite rand_DEED /randED /randFormat.
    cut -> //=: (size i < n + q) = false by smt.
    rewrite /SomeGarble.GSch.Sch.Scheme.validRand /SomeGarble.GSch.Sch.Scheme.validRand fst_pair /=.
    rewrite leni_nq //= eq_sym eqT=> k k_bnd.
      rewrite !get_arrayToMap /=
              size_mapi leni_nq k_bnd //=
              !snd_pair //=
              !oget_some.
      rewrite get_mapi ?leni_nq //=.
      case (k < n + q - m)=> k_nqm.
        rewrite snd_pair /=.
        cut ->: (n + q - m <= k) = false by smt=> //=.
        by rewrite set_getlsb (*/SomeGarble.W.getlsb*) get_setlsb; smt.
        rewrite snd_pair /=.
        cut ->: (n + q - m <= k) = true by smt=> //=.
        by rewrite (*/DKCScheme.W.getlsb*) !get_setlsb.
  qed.
  
  lemma funG_ED (fn:bool SomeGarble.funct_t) (r:(int*bool, word) map):
    funG_valid fn r =>
    funGED (ProjScheme.Sch.Scheme.funG (funDE fn) (randDE r)) =
     SomeGarble.GSch.Sch.Scheme.funG fn (randFormatD (fn.`1) r).
  proof.
    elim fn=> t gg /=.
    elim t=> n m q aa bb /=.
    rewrite /funG_valid /functD_topo_valid /=.
    progress.
    cut hlen : size (offun (fun (i0 : int), 0) n || sub aa n q) = n + q. by rewrite size_append ? size_offun ? size_sub ? H1 // max_ler.
    apply arrayP;split;first by rewrite hlen H1.
    progress.
    rewrite get_append // size_offun //.
    case (0 <= i < n)=> h.
      by rewrite offunE //;smt.
      by rewrite get_sub ? H1 //;smt.
    cut hlen : size (offun (fun (i0 : int), 0) n || sub bb n q) = n + q by rewrite size_append ? size_offun ? size_sub ? H2 // max_ler. 
    apply arrayP;split;first by rewrite hlen H2.
    progress.
    rewrite get_append // size_offun //.
    case (0 <= i < n)=> h.
      by rewrite offunE //;smt.
      by rewrite get_sub ? H2 //;smt.
    rewrite /Sch.Scheme.funG /randFormatD /funG /funDE /topoDE /= !snd_pair /= /arrayToMap2 /mapToArray2 /=.
    apply map_ext=> y.
    elim y=> g a b.
    rewrite size_offun //=. rewrite max_ler; first by exact H0. simplify.
  (*
    rewrite !(_: forall (g:(int*bool*bool, word) map) (y:int*bool*bool), g.[y] = g.[y]);first 2 by trivial.*)
    rewrite !SomeGarble.get_initGates //.
    case (n <= g < n + q)=> h //.
    rewrite /garbMap /garbleGate /init_gates /SomeGarble.enc /enc /evalTupleGate /randED !snd_pair /=.
    rewrite !/fst offunE /=;first smt.
  (*  simplify "_.[_]".*)
    pose r' := randFormat (n + q) m (randDE r).
    cut h' : 0 <= g - n < q by smt.
    rewrite !get_sub // ?H1 ?H2 //.
    rewrite offunE //.
    rewrite /evalTupleGate (*/SomeGarble.W.getlsb*) /getTok /=.
    rewrite !get_arrayToMap.
    rewrite !snd_pair.
    rewrite (*/SomeGarble.W.getlsb*) /getTok /=.
    cut ->: size r' = n + q by smt.
    cut ->: 0 <= g < n + q by smt.
    cut ->: 0 <= aa.[g] < n + q by smt.
    cut ->: 0 <= bb.[g] < n + q by smt.
    cut ->: g - n + n = g by smt.
    cut ->: n + (g - n) = g by smt.
    rewrite /= !oget_some.
    cut h1 : getlsb (r'.[aa.[g]].`2) = ! getlsb (r'.[aa.[g]].`1).
    simplify r' randFormat.
    case (size (randDE r) < n + q).
      by rewrite offunE ?fst_pair ?snd_pair ?get_setlsb;smt.
      by (rewrite get_mapi /=;first smt);case (aa.[g] < n + q - m); rewrite !get_setlsb //.
    cut h2 : getlsb (r'.[bb.[g]].`2) = !getlsb (r'.[bb.[g]].`1).
    simplify r' randFormat.
    case (size (randDE r) < n + q).
      by rewrite offunE ?fst_pair ?snd_pair ?get_setlsb;smt.
      by (rewrite get_mapi /=;first smt);case (bb.[g] < n + q - m);rewrite !get_setlsb //.
    rewrite h1 h2.
    by rewrite /Bool.(^^) /snd; case a; case b; case (getlsb (r'.[aa.[g]]).`1); case (getlsb (r'.[bb.[g]]).`1);
       move=> //=; smt.
  qed.

  pred inputK_valid (fn:'a SomeGarble.funct_t) (r:SomeGarble.GSch.Sch.Scheme.rand_t) = 
    let (n, m, q, aa, bb) = fn.`1 in
    0 <= n /\
    0 <= q /\
    1 + fold (fun (p:int * bool) (s:int), max (p.`1) s) (-1) (dom r) = (n + q)%Int.

  lemma inputK_ED fn r : inputK_valid fn r =>
    inputKED (ProjScheme.Sch.Scheme.inputK (funDE fn) (randDE r)) =
     SomeGarble.GSch.Sch.Scheme.inputK fn (randFormatD (fn.`1) r).
  proof.
    simplify inputKED funDE randED topoDE topoED Sch.Scheme.inputK
             SomeGarble.GSch.Sch.Scheme.inputK inputK SomeGarble.GSch.Sch.Scheme.inputK inputK_valid.
    elim fn=> topo gg /=.
    rewrite !fst_pair /=.
    rewrite !snd_pair /=.
    elim topo=> n m q aa bb /=.
    progress.
    apply map_ext=> y.
    cut nq_pos : 0 <= n + q by smt.
    cut len_r : size (randDE r) = n + q  by rewrite /randDE /mapToArray /= size_offun H1 // max_ler.
    simplify randFormatD randED.
    rewrite get_arrayToMap.
    rewrite get_filter !get_arrayToMap //.
    rewrite size_sub //=;
      first by rewrite size_randFormat // len_r //;smt.
    rewrite size_randFormat // len_r // /fst /=.
    case (0 <= y.`1 < n)=> h //=.
    cut -> /=: 0 <= y.`1 < n + q by smt.
    by rewrite get_sub // size_randFormat len_r;smt.
  qed.

  lemma outputK_ED fn r:
    outputKED (ProjScheme.Sch.Scheme.outputK (funDE fn) (randDE r)) =
     SomeGarble.GSch.Sch.Scheme.outputK fn (randFormatD (fn.`1) r)
  by smt.

  lemma decode_ED k y:
    outputED (ProjScheme.Sch.Scheme.decode (outputKDE k) (outputGDE y)) =
     SomeGarble.GSch.Sch.Scheme.decode k y
  by smt.

  lemma pi_sampler_ED x : functD_topo_valid (fst x) =>
    (let y = (ProjScheme.Sch.Scheme.pi_sampler (leakDE (fst x), (outputDE (snd x)))) in (funED (fst y), snd y)) = SomeGarble.GSch.Sch.Scheme.pi_sampler x.
  proof. 
    simplify Sch.Scheme.pi_sampler Mtopo SomeGarble.GSch.Sch.Scheme.pi_sampler SomeGarble.GSch.Sch.Scheme.pi_sampler funED topoDE topoED arrayToMap2 functD_topo_valid leakDE.
    elim x=> t i /=.
    elim t=> n m q aa bb /=.
    simplify fst snd.
    progress. 
      rewrite arrayP; split; first smt.
      move=> i0 i_bnd; rewrite get_append // size_offun //.
      case (0 <= i0 < n)=> i_split.
        by rewrite offunE //=; cut [->]:= H3 i0 _; smt.
        by rewrite get_sub 3:H1 // smt.
      apply arrayP; split; first smt.
      move=> i0 i_bnd; rewrite get_append // size_offun //.
      case (0 <= i0 < n)=> i_split.
        by rewrite offunE //=; cut [_ ->]:= H3 i0 _; smt.
        by rewrite get_sub 3:H2 // smt.
      apply map_ext=> y.
      elim y=> g a b.
      cut /= -> // :=
        SomeGarble.get_initGates n q (fun (g : int) (a b : bool), ! g < n + q - m && i.[g - (n + q - m)]).
      cut := SomeGarble.get_initGates n q  (fun (g0 : int) (a0 b0 : bool),
               evalTupleGate
                 (offun
                    (fun (g1 : int),
                       if g1 < q - m then (false, false, false, false)
                       else
                         ((outputDE i).[g1 - (q - m)], (outputDE i).[g1 - (q - m)],
                          (outputDE i).[g1 - (q - m)], (outputDE i).[g1 - (q - m)])) q).[
                 g0 - n] a0 b0).
      rewrite size_offun /=. 
      move=> Hf //. 
      case (n <= g < n + q)=> h //.
      rewrite max_ler; first by assumption. simplify.
      rewrite SomeGarble.get_initGates. smt. rewrite h. simplify.
      rewrite offunE. smt.
                            simplify evalTupleGate. 
      case (g - n < q - m). progress. smt. smt. smt.
  qed.

  lemma validInputs_DE fn i :
    ProjScheme.Sch.Scheme.validInputs fn i =
     SomeGarble.GSch.Sch.Scheme.validInputs (funED fn) (inputED i).
  proof.
    simplify mapToArray2 SomeGarble.valid_gates SomeGarble.GSch.Sch.Scheme.validInputs
             validInputs ProjScheme.Sch.Scheme.validInputs funED inputED topoED.
    rewrite SomeGarble.valid_wireinput valid_wireinput /SomeGarble.valid_circuitP /validCircuitP.
    elim fn=> topo gg /=.
    elim topo=> n m q aa bb /=.
    rewrite /= !snd_pair /= !fst_pair /=.
    rewrite eq_iff.
    progress; first 9 by smt. 
      by cut := H7 (size i) false false _;smt. 
      cut := H8 (i0 + size i) _; first by smt.
        rewrite ?get_append 1,2: smt.
        by rewrite size_offun max_ler; smt. 
      cut := H8 (i0 + size i) _; first by smt.
        rewrite ?get_append 1,2: smt.
        by rewrite size_offun max_ler; smt. 
      cut := H8 (i0 + size i) _;first by smt.
        rewrite ?get_append 1,2: smt.
        by rewrite size_offun max_ler; smt. 
      cut := H8 (i0 + size i) _;first by smt.
        rewrite ?get_append 1,2: smt.
        by rewrite size_offun max_ler; smt.   
  qed.
(* End Morphism *)
  
  lemma valids fn i r : Sch.Scheme.validInputs fn i => Sch.Scheme.validRand fn r => (
    functD_topo_valid (leakED (Sch.Scheme.phi fn)) &&
    functE_topo_valid (Sch.Scheme.phi fn) &&
    functE_valid fn &&
    eval_valid (funED fn) (inputED i) &&
    validRandD fn r &&
    encode_valid (inputKED (Sch.Scheme.inputK fn r)) (inputED i) &&
    funG_valid (funED fn) (randED r) &&
    inputK_valid (funED fn) (randED r) &&
    eval_valid (funGED (Sch.Scheme.funG fn r)) (inputGED (Sch.Scheme.Input.encode (Sch.Scheme.inputK fn r) i)) &&
    functE_valid (Sch.Scheme.funG fn r) &&
    functE_valid (((Sch.Scheme.pi_sampler (Sch.Scheme.phi fn, (Sch.Scheme.eval fn i)))).`1) &&
    functE_valid (Sch.Scheme.funG (((Sch.Scheme.pi_sampler (Sch.Scheme.phi fn, (Sch.Scheme.eval fn i)))).`1) r) &&
    encode_valid
      (inputKED ((Sch.Scheme.inputK (((Sch.Scheme.pi_sampler (Sch.Scheme.phi fn, (Sch.Scheme.eval fn i)))).`1) r)))
      (snd ((Sch.Scheme.pi_sampler (Sch.Scheme.phi fn, (Sch.Scheme.eval fn i)))))
    ).
  proof.
    elim fn=> topo gg /=.
    elim topo=> n m q aa bb /=.
    simplify Sch.Scheme.validInputs Sch.Scheme.validRand functE_valid eval_valid funED inputED validRandD encode_valid inputKED Sch.Scheme.inputK inputED funG_valid inputK_valid eval_valid functE_valid Sch.Scheme.funG functE_topo_valid validInputs topoED functE_gg_valid inputGED Sch.Scheme.Input.encode funG funGED inputK Sch.Scheme.phi Sch.Scheme.pi_sampler Mtopo.
    rewrite valid_wireinput /validCircuitP /=.
  (* this progress brakes too much thing especially the goal of kind :

  forall (i0 : int),
     0 <= i0 < q =>
     0 <= aa.[i0] /\
     bb.[i0] < n + i0 /\ bb.[i0] < n + q - m /\ aa.[i0] < bb.[i0])

  this forced you to proved 4 goal separately whereas the proof is the same for the 4
  and maybe smt would be more bright without this
  *)
    progress.
    by rewrite size_ge0.
    by rewrite size_ge0.
    by rewrite size_append size_offun ? size_ge0 max_ler 1:smt.
    by rewrite size_append size_offun ? size_ge0 max_ler 1:smt // -H4. 
    by rewrite get_append_left ? size_offun ? size_ge0 ?max_ler 1:smt ?offunE.
    by rewrite get_append_left ? size_offun ? size_ge0 ?max_ler 1:smt ?offunE.
    by rewrite size_ge0.
    by rewrite size_ge0.
    by rewrite size_append size_offun ? size_ge0 ?max_ler 1:smt.
    by rewrite size_append size_offun ? size_ge0 ?max_ler 1:smt // -H4.
    by cut := H6 i0 _=> //;progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by cut := H6 i0 _=> //;progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by cut := H6 i0 _=> //;progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by cut := H6 i0 _=> //;progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by smt.
    by rewrite max_arrayToMap;smt.
    by rewrite get_append_left ? size_offun ? size_ge0 ?max_ler 1:smt ? offunE.
    by rewrite get_append_left ? size_offun ? size_ge0 ?max_ler 1:smt ? offunE.
    by rewrite /randED max_arrayToMap;smt.
    by (cut := H6 (i0 - size i) _;first smt);progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by (cut := H6 (i0 - size i) _;first smt);progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by (cut := H6 (i0 - size i) _;first smt);progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by (cut := H6 (i0 - size i) _;first smt);progress;rewrite get_append_right ? size_offun ? size_ge0 //;smt.
    by rewrite size_offun ? size_sub ?size_randFormat;smt.
    by rewrite /snd /= size_offun ?max_ler 1:smt.
    by rewrite /snd /= size_offun ?max_ler 1:smt.
    by rewrite /snd /= size_offun ?max_ler 1:smt.
    by rewrite /snd /= size_offun ?max_ler 1:smt.
  qed.
  
(* Begin Correction Lemma *)
  lemma sch_correct: SomeGarble.DKCSecurity.D.Correct () => ProjScheme.Sch.Scheme.Correct ().
  proof.
    move=> h.
    rewrite /ProjScheme.Sch.Scheme.Correct=> r fn i h1 h2.
    cut := valids fn i r _ _=> //.
    do 12 ! (move => [?]); move => ?.
    move : h1 h2.
    rewrite validInputs_DE validRand_DE //. 
    move => hInputs hRand.
    cut:= SomeGarble.gsch_correct _ (randFormatD ((funED fn).`1) (randED r)) (funED fn) (inputED i) _ _=> //=.
    rewrite -(outputK_ED (funED fn) (randED r)).
    rewrite -(funG_ED (funED fn) (randED r)) //. 
    rewrite -(inputK_ED (funED fn) (randED r)) // fun_DEED // rand_DEED.
    rewrite -encode_ED // inputK_DEED // input_DEED //.
    rewrite -evalG_ED // inputG_DEED // funG_DEED //.
    rewrite -decode_ED outputK_DEED outputG_DEED.
    by rewrite -eval_ED // fun_DEED.
  qed.
(* End Correction Lemma *)

  clone import SchSec.SchSecurity with
    theory Sch.Scheme <- ProjScheme.Sch.Scheme.
    
    print SomeGarble.GSch.
    
  (* Begin Random equivalence *)
  module R1 = {
    (*module C' = DKCScheme.C
    module R' = DKCScheme.R
*)
    var trnd : bool
    var tok1, tok2 : word

    proc genTok(b:bool) : unit = {
      trnd = $ {0,1};
      trnd = b ? trnd : false;
      tok1 = $Dword.dwordLsb ( trnd);
      tok2 = $Dword.dwordLsb (!trnd);
    }

    proc gen(l:topo_t): SomeGarble.GSch.Sch.Scheme.rand_t = {
      var i:int;
      var x:(int*bool, word) map;
      var (n, m, q, aa, bb) = l;
    
      (n, m, q, aa, bb) = l;
      x = FMap.empty;
      i = 0;
      while (i < n + q) {
        genTok(i < n + q - m);

        x.[(i, false)] = tok1;
        x.[(i,  true)] = tok2;

        i = i + 1;
      }
      return x;
    }
  }.

equiv Rand_R1 : SomeGarble.R.gen ~ R1.gen : ={l} ==> ={res}.
proof strict.
  proc.
  inline R1.genTok.
  while (
  ={i} /\
  ret{1} = x{2} /\
  n{1}  = n{2} /\
  m{1}  = m{2} /\
  q{1}  = q{2} /\
  aa{1} = aa{2} /\
  bb{1} = bb{2} /\ true).
    by wp;rnd;rnd;wp;rnd;wp;skip;smt.
    by wp;skip;smt.
qed.

print ProjScheme.Sch.Scheme.

  module Rand:EncSecurity.Rand_t = {
    proc genTok(): word * word = {
      var tok1, tok2;
      tok1 = $Dword.dword;
      tok2 = $Dword.dword;
      return (tok1,tok2);
    }

    proc gen(l:topo_t): ProjScheme.Sch.Scheme.rand_t = {
      var i:int;
      var x:(word*word) array;
      var (n, m, q, aa, bb) = l;
      x = offun (fun i, (W.zeros, W.zeros)) (n + q);
      i = 0;
      while (i < n + q) {
        x.[i] = genTok();
        i = i + 1;
      }
      return x;
    }
  }.

op base = 1%r / (2 ^ (W.length - 1))%r.

lemma dlsb': forall x b,  mu Dword.dword (fun (y : word), x = setlsb y b) = if getlsb x = b then base else 0%r.
proof.
move => x b.
case (getlsb x = b)=> h;
  last (cut -> : (fun (y : word), x = setlsb y b) = (fun x, false) by (apply ExtEq.fun_ext;smt);smt).
pose s := (fset1 (setlsb x true)) `|` ((fset1 (setlsb x false)) `|` FSet.fset0).
cut -> : (fun (y : word), x = setlsb y b) = fun y, mem s y.
  apply ExtEq.fun_ext=> y; smt.
  (*simplify cpMem s.*)
  (*rewrite ! mem_add.*)
(*  cut -> : forall (y:word), mem FSet.fset0 y = false by smt.*)
  (*by case (getlsb x);smt.*) 
rewrite (Dword.mu_cpMemw s).
cut -> : card s = 2. by (rewrite /s ! fcardUI_indep ? fcards0;smt).
simplify base.
cut -> : forall x0, 0 < x0 => 2 ^ x0 = 2 * (2 ^ (x0-1)) by smt.
smt.
cut : 0 < 2 ^ (W.length - 1) by smt.
simplify W.length W.length.
move : (2 ^ (W.length - 1)).
move=> x' lt0x'.
cut ->: 2%r / (2 * x')%r = 2%r /(2%r * x'%r) by smt.
rewrite -assoc_div_mul; first smt.
by rewrite mul_div; first smt. smt.
qed.

equiv eqR (bb:bool): R1.genTok ~ Rand.genTok:
  b{1} = bb ==> 
  R1.trnd{1} =  (if bb then getlsb res{2}.`1 else false) /\
  R1.tok1{1} = setlsb res{2}.`1 (if bb then  (getlsb res{2}.`1) else false) /\
  R1.tok2{1} = setlsb res{2}.`2 (if bb then !(getlsb res{2}.`1) else  true).
proof.
cut := Dword.dwordLsb_mu_x.
simplify Distr.mu_x.
rewrite -/base=> dlsb.

cut := Dword.dwordLsb_lossless.
rewrite /Distr.weight=> dlsb_ll.

bypr
  (R1.trnd{1}, R1.tok1{1}, R1.tok2{1})
  (bb && getlsb res{2}.`1, setlsb res{2}.`1 (bb && getlsb res{2}.`1), setlsb res{2}.`2 (bb => !(getlsb res{2}.`1))).
  done.
move=> &1 &2 [a1 a2 a3] hb1.
apply (eq_trans _
                (if getlsb a2 = a1 /\ getlsb a3 = !a1
                   then (if bb then 1%r/2%r else (if a1 = false then 1%r else 0%r))*base*base
                   else 0%r)).

byphoare (_: b = bb ==> (a1 = R1.trnd /\ a2 = R1.tok1 /\ a3 = R1.tok2))=> //.
proc.
seq 3: (a1 = R1.trnd /\ a2 = R1.tok1)
       (if getlsb a2 =  a1 then (if bb then 1%r/2%r else (if a1 = false then 1%r else 0%r))*base else 0%r)
       (if getlsb a3 = !a1 then base else 0%r)
       1%r
       0%r=> //.
  seq 2: (a1 = R1.trnd)
         (if bb then 1%r/2%r else (if a1 = false then 1%r else 0%r))
         (if getlsb a2 = a1 then base else 0%r)
         1%r
         0%r=> //.
    wp; rnd; skip=> //=.
    by case bb=> h &hr ->> /=; [rewrite ExtEq.eqL | case a1=> /=]; smt.
    rnd; skip=> //=.
    by move=> &hr -> //=; rewrite ExtEq.eqL; smt. 
    rnd; skip=> //=.
    by move=> &hr; rewrite -neqF=> -> //=; rewrite -/Pred.pred0 Distr.mu_false.
    by case (getlsb a2 = a1); case bb.
  rnd; skip=> //=.
  move=> &hr [-> ->] //=. rewrite ExtEq.eqL. smt.
  rnd; skip=> //=.
  by move=> &hr; rewrite -nand -!neqF; move => [-> | ->] //=; rewrite -/Pred.pred0 Distr.mu_false.
  by case (getlsb a2 = a1); case (getlsb a3 = ! a1); case (bb).
byphoare (_: true ==>
             a1 = (bb && getlsb res.`1) /\
             a2 = setlsb res.`1 (bb && getlsb res.`1) /\
             a3 = setlsb res.`2 (bb => ! getlsb res.`1))=> //.
proc.
seq 1: (a1 = (bb && getlsb tok1) /\ a2 = setlsb tok1 (bb && getlsb tok1))
       (if getlsb a2 = a1
          then (if bb then 1%r/2%r else (if a1 = false then 1%r else 0%r))*base
          else 0%r)
       (if getlsb a3 = !a1 then base else 0%r)
       1%r
       0%r=> //.
  rnd; skip=> //=.
  case bb=> hb /=.
  case (getlsb a2 = a1)=> h.
    cut ->: (fun (x : word), a1 = getlsb x /\ a2 = setlsb x (getlsb x)) = (=) a2.
      by apply ExtEq.fun_ext=> y /=; rewrite -h set_getlsb; smt.
    move: Dword.mu_x_def. rewrite /Distr.mu_x /base //= => hdword.
    cut : 0 < W.length by smt.
    move => Hsize.
    cut -> //: (2^(W.length - 1))%r * 2%r = (2^W.length)%r.
      cut ->: (2^(W.length - 1))%r * 2%r = (2^(W.length - 1) * 2)%r by smt.
      by congr; rewrite mulzC -powS; smt. 
      cut ->: ((=) a2) = Pred.pred1 a2 by smt.
      rewrite hdword. smt.       
      cut ->: (fun (x : word), a1 = getlsb x /\ a2 = setlsb x (getlsb x)) = (fun x,false).
      by apply ExtEq.fun_ext=> x /=; smt.       
    by rewrite -/Pred.pred0 Distr.mu_false.
  case (a1 = false)=> //=.
    by rewrite dlsb'; smt.
    by rewrite -/Pred.pred0; smt.
  rnd; skip=> //=.
  by move=> &hr [->> ->>] //=; rewrite dlsb'; smt.
  rnd; skip=> //=.
  by move=> &hr; rewrite -nand -!neqF; move => [-> | ->] //=; rewrite -/Pred.pred0 Distr.mu_false.
  by case (getlsb a2 = a1); case (getlsb a3 = !a1); case (bb);case a1.
qed.

op in_dom (x:'a) (m:('a,'b) map) = mem (dom m) x.
lemma in_dom_empty x: !in_dom x empty<:'a,'b>.
proof strict.
by rewrite /in_dom mem_dom get_empty /=.
qed.

lemma leq_in_dom (m1 m2:('a,'b) map) x:
  m1 <= m2 =>
  in_dom x m1 => in_dom x m2.
proof strict.
by rewrite /in_dom=> m1_m2; apply leq_dom.
qed.

lemma in_dom_set (m:('a,'b) map) x y x':
  in_dom x' (m.[x <- y]) = (in_dom x' m \/ x' = x).
proof strict. 
by rewrite /in_dom; smt.
qed.

lemma nosmt in_dom_set_in (m:('a,'b) map) x y:
  in_dom x m =>
  forall x', in_dom x' (m.[x <- y]) <=> in_dom x' m.
proof strict.
by rewrite /in_dom=> x'_m; rewrite dom_set_in.
qed.

lemma nosmt in_dom_set_nin (m:('a,'b) map) x y x':
  !in_dom x' m =>
  (in_dom x' (m.[x <- y]) <=> x' = x).
proof strict.
by rewrite /in_dom=> x_m; smt.
qed.

equiv RandEq fn: SomeGarble.R.gen ~ Rand.gen:
  let (n, m, q, aa, bb) = fn in
    l{1} = topoED fn /\
    l{2} = fn /\
    0 <= n /\
    0 <= q ==>
  let (n, m, q, aa, bb) = fn in
    (res{1} = randED (randFormat (n+q)%Int m res{2})) /\
    (size res{2} = n + q).
proof.
  elim fn=> n' m' q' aa' bb' /=.
  bypr (res{1}, n'+q') (randED (randFormat (n' + q') m' res{2}), size res{2})=> // &m1 &m2 a.
  simplify topoED.
  progress.
  apply (eq_trans _ Pr[R1.gen(l{m1}) @ &m1: a = (res, n' + q')]);
    first by byequiv Rand_R1=> //.
  byequiv (_: l{1}=l{m1} /\ l{2}=l{m2} ==> (res{1} = randED (randFormat (n'+q') m' res{2})) /\ (size res{2} = n' + q'))=> //;
    last by progress; rewrite H3.
  proc.
  while (
    ={i} /\
    0 <= i{2} /\
    i{1} <= n' + q' /\
    (n  = n' /\
    m  = m' /\
    q  = q' /\
    aa = (offun (fun (i : int), 0) n' || aa') /\
    bb = (offun (fun (i : int), 0) n' || bb')){1} /\
    (n  = n' /\
    m  = m' /\
    q  = q' /\
    aa = aa' /\
    bb = bb'){2} /\
    (forall j b, 0 <= j < i{1} <=> in_dom (j, b) x{1}) /\
    (forall j, 0 <= j < i{1} => 
      x{1}.[(j, false)] = Some (setlsb (x{2}.[j].`1) (if j < n' + q' - m' then   getlsb (x{2}.[j].`1) else false)) /\
      x{1}.[(j,  true)] = Some (setlsb (snd x{2}.[j]) (if j < n' + q' - m' then ! getlsb (x{2}.[j].`1) else true ))) /\
    (size x = n + q){2}).

    wp.

    exists* (i{1}).
    elim*.
    move => i.

    pose bb := i < n' + q' - m'.

    call (eqR bb).

    skip.
    simplify bb.
    (do ! (do ? (move => h;elim h);move => ?)).
    subst.
    simplify.
    (do ! (do ? (move => h;elim h);move => ?)).
    subst.
    split;first smt.
    split;first smt.
    split=> //.
    move => j b;rewrite ! in_dom_set.
    case (i{2} = j)=> h.
      by rewrite h;case b;smt.
      by cut := H17 j b;smt.
    split=> //.
    move => j hj.
    simplify "_.[_]".
    rewrite ! get_set ;first smt.
    case (i{2} = j)=> h.
      by rewrite -h //=;(cut -> : ((i{2}, true) = (i{2}, false)) = false by done);rewrite /= fst_pair snd_pair //.
      by cut := H18 j _;smt.
  smt.
  split => //; first by smt.
  split => //; first by smt.
  split => //.
    move => j b; rewrite ! in_dom_set. 
    case (i{2} = j)=> h.
      by rewrite h;case b;smt.
      by cut := H17 j b;smt.
    split=> //.
    move => j hj.
    simplify "_.[_]".
    rewrite ! get_set ;first smt.
    case (i{2} = j)=> h.
      by rewrite -h //=;(cut -> : ((i{2}, true) = (i{2}, false)) = false by done);rewrite /= fst_pair snd_pair //.
      by cut := H18 j _;smt.
  smt.
  wp.
  skip.
  move : H H0.
  progress;first 7 smt.
  apply map_ext=> y.
  elim y=> i b.
  simplify randED randFormat.
  rewrite get_arrayToMap snd_pair /=.
  cut -> : (size x_R < n' + q') = false by smt.
  rewrite /= size_mapi.
  case (0 <= i < size x_R)=> hh.
  rewrite get_mapi //.

  cut := H8 i _;first by smt.
  simplify "_.[_]".
  progress.
  case b;[rewrite H11|rewrite H10];case (i < n' + q' - m');smt.

  cut := H7 i b.
  cut -> : 0 <= i < i_R = false by smt.
  simplify=> h.
  smt.
qed.

lemma Rand_islossless : islossless Rand.gen.
proof strict.
proc.
while (true) (n + q - i + 1).
move => z.
inline Rand.genTok.
wp;rnd;rnd;skip;smt.
wp;skip;smt.
qed.

equiv Rand_stateless : Rand.gen ~ Rand.gen : ={l} ==> res{1} = res{2}.
proof strict.
proc.
while (={i, x, n, m, q, aa, bb}).
inline Rand.genTok.
by wp;rnd;rnd.
by wp.
qed.

(* End Random equivalence *)

(* Begin security lemma *)

  equiv Sim_stateless: EncSecurity.SIM(Rand).simm ~ EncSecurity.SIM(Rand).simm: ={leakage} ==> ={glob EncSecurity.SIM, res}.
  proof strict.
  by proc; wp; call Rand_stateless; wp.
  qed.

  print SomeGarble.GSch.
  
module Red(A:EncSecurity.Adv_SIM_t) : SomeGarble.GSch.EncSecurity.Adv_SIM_t = {
  proc gen_query() : SomeGarble.GSch.EncSecurity.query_SIM = {
    var (f, x) : SchSecurity.EncSecurity.Encryption.plain;
    (f, x) = A.gen_query();
    return (funED f, inputED x);
  }
  proc get_challenge(cipher : SomeGarble.GSch.EncSecurity.Encryption.cipher) : bool =
  {
    var (f, y, ko) : SomeGarble.GSch.EncSecurity.Encryption.cipher;
    var b : bool;
    (f, y, ko) = cipher;
    b = A.get_challenge((funGDE f, inputGDE y, outputKDE ko));
    return b;
  }
}.

print SomeGarble.gsch_is_sim.

(*lemma gsch_is_sim (A <: GSch.EncSecurity.Adv_SIM_t {R}) &m:*)

(*lemma sch_is_sim (A <: EncSecurity.Adv_SIM_t {Rand} ) &m:
 islossless A.gen_query =>
 islossless A.get_challenge =>
  `|2%r * Pr[EncSecurity.Game_SIM(Rand,EncSecurity.SIM(Rand), A).main()@ &m:res] - 1%r| <=
    2%r * (SomeGarble.bound)%r * `|2%r * Pr[DKCScheme.DKCSecurity.Game(DKCScheme.DKCSecurity.Dkc, DKCScheme.RedI(DKCScheme.SchSecurity.EncSecurity.RedSI(Red(A)))).main()@ &m:res] - 1%r|.
proof strict.
intros=> ll_ADVp1 ll_ADVp2.
cut := DKCScheme.sch_is_sim (Red(A)) &m _ _=> //.
by proc;call ll_ADVp1.
by proc;call ll_ADVp2;wp.
cut -> : Pr[DKCScheme.SchSecurity.EncSecurity.Game_SIM(DKCScheme.Rand, DKCScheme.SchSecurity.EncSecurity.SIM(DKCScheme.Rand), Red(A)).main()@ &m : res] = Pr[EncSecurity.Game_SIM(Rand, EncSecurity.SIM(Rand), A).main()@ &m : res];intros=> //.
byequiv (_: ={glob A} ==> ={res})=> //.
proc.
inline Red(A).gen_query Red(A).get_challenge DKCScheme.SchSecurity.EncSecurity.Game_SIM(DKCScheme.Rand, DKCScheme.SchSecurity.EncSecurity.SIM(DKCScheme.Rand), Red(A)).game EncSecurity.Game_SIM(Rand, EncSecurity.SIM(Rand), A).game EncSecurity.SIM(Rand).simm DKCScheme.SchSecurity.EncSecurity.SIM(DKCScheme.Rand).simm.
seq 4 3 : (={glob A, b} /\
(query{1} = (funED (query{2}.`1), inputED (snd query{2}))) /\ real{1} = real{2} ).
 wp;call (_: ={glob A} ==> ={res, glob A});first by proc true.
 by wp; rnd; skip; progress; smt.
if;[smt|by wp; rnd|].
if; first smt.
  exists* query{2}; elim* => qu.
  wp; call (_: true).
  wp; call (RandEq (EncSecurity.Encryption.randfeed qu)).
  skip=> {ll_ADVp1 ll_ADVp2}.
  elim qu=> fn xx; elim fn=> tt gg; elim tt=> n m q aa bb &1 &2.
  simplify DKCScheme.SchSecurity.EncSecurity.queryValid_SIM DKCScheme.SchSecurity.EncSecurity.Encryption.valid_plain DKCScheme.SchSecurity.EncSecurity.Encryption.randfeed EncSecurity.Encryption.randfeed Sch.Scheme.phi DKCScheme.SchSecurity.EncSecurity.Encryption.enc DKCScheme.SchSecurity.Sch.Scheme.phi ProjScheme.Sch.Scheme.phi DKCScheme.C2.phi EncSecurity.Encryption.enc Sch.Scheme.funG Sch.Scheme.Input.encode Sch.Scheme.outputK Sch.Scheme.inputK DKCScheme.SchSecurity.EncSecurity.Encryption.pi_sampler DKCScheme.SchSecurity.Sch.Scheme.phi EncSecurity.Encryption.pi_sampler Sch.Scheme.pi_sampler Sch.Scheme.phi Sch.Scheme.eval EncSecurity.Encryption.leak DKCScheme.SchSecurity.EncSecurity.Encryption.leak fst snd.
  move=> [<<-] //= [[[[->> ->>]]]] //= [->> ->>] //=.
  rewrite -validInputs_DE=> vIn b.
  split.
    by move: vIn; delta=> /=; smt.
  move=> h' {h'} result_L result_R [->>] len_res.
  split=> //.
  move: (valids ((n,m,q,aa,bb),gg) xx result_R _ _)=> //.
  rewrite /fst /snd=> [fD_tt_v] [fE_tt_v] [fE_v] [eval_v] [rD_v] [encode_v] [fG_v] [iK_v] [evalG_v] [fGE_v] [fE_phi_v] [fGE_phi_v] iK_phi_valid.
  cut -> : randED (randFormat (n + q) m result_R) = randFormatD ((funED ((n, m, q, aa, bb), gg)).`1) (randED result_R)
    by rewrite /randFormatD /funED /topoED rand_DEED.
  pose fn:= ((n,m,q,aa,bb),gg).
  pose r:= result_R.
  split.
    rewrite -(funG_ED (funED fn) (randED r)) //.
    rewrite (fun_DEED fn) // rand_DEED //.
    by rewrite funG_DEED.
  move=> H {H}; split.
    rewrite -(inputK_ED (funED fn) (randED r)) //.
    rewrite (fun_DEED fn) // rand_DEED //.
    rewrite -encode_ED //.
    by rewrite inputK_DEED input_DEED inputG_DEED.
  by rewrite -(outputK_ED (funED fn) (randED r)).
  exists* query{2}; elim* => qu.
  wp; call (_: true).
  wp; call (RandEq (EncSecurity.Encryption.randfeed qu)).
  wp; skip=> {ll_ADVp1 ll_ADVp2}.
  elim qu=> fn xx; elim fn=> tt gg; elim tt=> n m q aa bb &1 &2.
  simplify DKCScheme.SchSecurity.EncSecurity.queryValid_SIM DKCScheme.SchSecurity.EncSecurity.Encryption.valid_plain DKCScheme.SchSecurity.EncSecurity.Encryption.randfeed EncSecurity.Encryption.randfeed Sch.Scheme.phi DKCScheme.SchSecurity.EncSecurity.Encryption.enc DKCScheme.SchSecurity.Sch.Scheme.phi ProjScheme.Sch.Scheme.phi DKCScheme.C2.phi EncSecurity.Encryption.enc Sch.Scheme.funG Sch.Scheme.Input.encode Sch.Scheme.outputK Sch.Scheme.inputK DKCScheme.SchSecurity.EncSecurity.Encryption.pi_sampler DKCScheme.SchSecurity.Sch.Scheme.phi EncSecurity.Encryption.pi_sampler Sch.Scheme.pi_sampler Sch.Scheme.phi Sch.Scheme.eval EncSecurity.Encryption.leak DKCScheme.SchSecurity.EncSecurity.Encryption.leak.
  move=> [<<-] //= [[[[->> ->>]]]] //= [->> ->>] //=.
  rewrite !fst_pair !snd_pair -validInputs_DE=> vIn b /=.
  split.
    by move: vIn; delta=> /=; smt.
  move=> h' {h'} result_L result_R [->>] len_res.
  split=> //.
  move: (valids ((n,m,q,aa,bb),gg) xx result_R _ _)=> //.
  move=> [fD_tt_v] [fE_tt_v] [fE_v] [eval_v] [rD_v] [encode_v] [fG_v] [iK_v] [evalG_v] [fGE_v] [fE_phi_v] [fGE_phi_v] iK_phi_valid.
  cut -> : randED (randFormat (n + q) m result_R) = randFormatD (fst (fst
              ((DKCScheme.SchSecurity.Sch.Scheme.pi_sampler
                  ((funED ((n, m, q, aa, bb), gg)).`1,
                   (DKCScheme.SchSecurity.Sch.Scheme.eval
                      (funED ((n, m, q, aa, bb), gg)) (inputED xx))))))) (randED result_R)
    by rewrite /randFormatD /funED /topoED /fst rand_DEED //.
  cut H: (funED ((n, m, q, aa, bb), gg)).`1 = leakED (Sch.Scheme.phi ((n, m, q, aa, bb), gg)) by trivial.
  rewrite !/fst H //=.
  pose fn:= ((n,m,q,aa,bb),gg).
  pose r:= result_R.
  split.
    rewrite -eval_ED // fun_DEED // input_DEED //.
    pose phi_ED:= (DKCScheme.SchSecurity.Sch.Scheme.pi_sampler (leakED (Sch.Scheme.phi fn),outputED (ProjScheme.Sch.Scheme.eval fn xx))).`1.
    rewrite -(funG_ED phi_ED (randED r)) 1:// rand_DEED.
    rewrite /phi_ED.
    rewrite -(pi_sampler_ED (leakED (Sch.Scheme.phi fn),outputED (ProjScheme.Sch.Scheme.eval fn xx))) 1://.
    rewrite !/fst !/snd /=.
    rewrite (leak_DEED (Sch.Scheme.phi fn)) 1://.
    rewrite (output_DEED (ProjScheme.Sch.Scheme.eval fn xx)).
    rewrite (fun_DEED ((ProjScheme.Sch.Scheme.pi_sampler (Sch.Scheme.phi fn,ProjScheme.Sch.Scheme.eval fn xx))).`1) 1://.
    by rewrite funG_DEED.
  move=> H42 {H42}; split=> //.
  rewrite -eval_ED // fun_DEED // input_DEED //.
  pose phi_ED:= (DKCScheme.SchSecurity.Sch.Scheme.pi_sampler (leakED (Sch.Scheme.phi fn),outputED (ProjScheme.Sch.Scheme.eval fn xx))).`1.
  rewrite -(inputK_ED phi_ED (randED r)) 1:// rand_DEED.
  rewrite /phi_ED.
  rewrite -(pi_sampler_ED (leakED (Sch.Scheme.phi fn),outputED (ProjScheme.Sch.Scheme.eval fn xx))) 1://.
  rewrite !/fst !/snd /=.
  rewrite (leak_DEED (Sch.Scheme.phi fn)) 1://.
  rewrite (output_DEED (ProjScheme.Sch.Scheme.eval fn xx)).
  rewrite (fun_DEED ((ProjScheme.Sch.Scheme.pi_sampler (Sch.Scheme.phi fn,ProjScheme.Sch.Scheme.eval fn xx))).`1) 1://.
  rewrite -(encode_ED) 1://.
  by rewrite inputG_DEED inputK_DEED.
qed.*)
(* End security lemma *)
end EfficientScheme.

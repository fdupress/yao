(** Entropy smoothing assumption for keyed hash functions *)

require import Bool.
require import DBool.
require import Int.
require import Pair.
require import Real.
require import Distr.

require import Array.

(** Entropy Smoothing security assumption *)
(*require import Prime_field.
require import Cyclic_group_prime.*)

require import ArrayExt.

(**
   A general keyed hash function family. The hash functions have:
     - A domain;
     - A counter domain;
     - The key that indexes the hash function;
     - A distribution over those keys (to generate random keys);
     - The hash operation, that takes as input a key and an element of the domain
     and that outputs an element of the counter domain.
*)
theory KeyedHash.
 type dom_t.
 type codom_t.
 type hkey_t.
 op dkey:hkey_t distr.

 op hash:hkey_t -> dom_t -> codom_t.
end KeyedHash.

(**
   The entropy-smoothing assumption states that an adversarty is not able to 
   distinguish between a random value sampled from the counter domain and
   a value obtained by the execution of the hash function.
*)

(** Entropy-Smoothing. *)
theory ES.

  (** The assumption is defined for some domain, counter domain and some family of keys *)
  type dom_t.
  type codom_t.
  type hkey_t.
  op ddom:dom_t distr.
  op dcodom:codom_t distr.
  op dkey:hkey_t distr.

  (** An instantiation of keyed hash functions is made using the elements to whomn the 
    assumption is being defined *)
  clone KeyedHash as H with
   type dom_t = dom_t,
   type codom_t = codom_t,
   type hkey_t = hkey_t,
   op dkey = dkey.

   (** An adversary for the entropy smoothing argument tries to distinguish between an
     output of an hash function and a truly random bitstring *)
  module type Adv_t = {
    proc init(): unit
    proc solve(k:hkey_t, x:codom_t): bool
  }.

  (** Cryptographic games *)
  (**
     The cryptographic games are used to define the security of both parties.
     These games will use the adversary defined above (that attacks the security
     of the entropy smoothing assumption) to try to distinguish between a random
     value and one obtained by the execution of the hash function.

     The routine starts by initialising the adversary and then sample the
     values that will be used by the remain procedure. After, the adversary is
     given a truly random value from the counter domain or a value generated
     from the execution of the hash function and it is asked to
     distinguish if it is in the presence of a random value or an hashed one.
  *)
  module Game (A:Adv_t) = {
    proc game(b:bool): bool = {
      var x:dom_t;
      var k:hkey_t;
      var b':bool;
      var y:codom_t;

      A.init();
      x = $ddom;
      k = $H.dkey;
      y = $dcodom;
      if (b) b' = A.solve(k,H.hash k x); else b' = A.solve(k,y);
      
      return b = b';
    }
    proc main(): bool = {
      var b, adv: bool;
      
      b = ${0,1};
      adv = game(b);
      
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)
  
  lemma Gamegame_lossless (A <: Adv_t) :
    islossless A.init =>
    islossless A.solve =>
    is_lossless dcodom =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    islossless Game(A).game.
  proof.
    move => Ainit_ll Asolve_ll dcodom_ll hkey_ll ddom_ll.
    proc => //.
    seq 1 : true => //; first by call(_:true).
    seq 3 : true => //; first by auto; smt.
    if.
    (*case b*)
      call(_:true); first by apply Asolve_ll.
      skip; smt.
    (*case !b*)
      call(_:true); first by apply Asolve_ll.
      skip; smt.
  qed.

  lemma Gamemain_lossless (A <: Adv_t) :
    islossless A.init =>
    islossless A.solve =>
    is_lossless dcodom =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    islossless Game(A).main.
  proof.
    move => Ainit_ll Asolve_ll dcodom_ll hkey_ll ddom_ll.  
    proc => //.
    seq 1 : true => //; first by auto; smt.
    call (_ : true).
    seq 1 : true => //; first by call(_:true).
    seq 3 : true => //; first by auto; smt.
    if.
    (*case b*)
      call(_:true); first by apply Asolve_ll.
      skip; smt.
    (*case !b*)
      call(_:true); first by apply Asolve_ll.
      skip; smt.
    skip; smt.
  qed.

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)

  (**
    The advantage of an adversary against an entropy smoothing hash function 
    with respect to the games above is |2*Pr[adv = b] - 1|. The hash function
    is entropy smoothing if the advantage is negligeble.

    The probability Pr[adv = b] can be expandaded as 1/2 * (Pr[adv = b | b = true]
    + Pr[adv = b | b = false]).

    This advantage can be defined in the form of conditional probabilities as
    Pr[adv = b | b = true] - Pr[adv != b | b = false].
  *)

  (** Conditional probability expansion *)
  lemma Game_xpnd &m (A <: Adv_t):
    Pr[Game(A).main()  @ &m: res] 
    = 1%r/2%r * (Pr[Game(A).game(true)  @ &m: res]
      + Pr[Game(A).game(false)  @ &m: res]).
  proof.
    pose p1 := Pr[Game(A).game(true) @ &m : res].
    pose p2 := Pr[Game(A).game(false) @ &m : res].
    byphoare (_: (glob A) = (glob A){m} ==> _) => //.
      proc => //.
      seq 1 : b (1%r/2%r) p1 (1%r/2%r) p2 ((glob A) = (glob A){m}).
        by auto.
        by rnd; skip; smt.
        call (_: (glob A) = (glob A){m} /\ b ==> res)=> //.
          rewrite /p1.
          bypr => &m' [eqA] b'.
          byequiv (_: ={glob A,b} /\ b{1} ==> ={res})=> //.
            by sim.
            by rewrite eqA b'.
        by rnd; skip; smt.
        call (_: (glob A) = (glob A){m} /\ !b ==> res)=> //.
          rewrite /p2.
          bypr=> &m' [eqA] b'.
          byequiv (_: ={glob A,b} /\ !b{1} ==> ={res})=> //.
            by sim.
            by move: b'; rewrite -neqF eqA=> ->.
    by smt.
  qed.

  (** Advantage definition *)
  lemma Game_adv &m (A<:Adv_t):
    is_lossless dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless A.init =>
    islossless A.solve =>
    2%r * Pr[Game(A).main()  @ &m: res] - 1%r
    = Pr[Game(A).game(true)  @ &m: res]
      - Pr[Game(A).game(false)  @ &m: !res].
  proof.
    move => H1 H2 H3 Ainit_ll Asolve_ll.
    rewrite (Game_xpnd &m A).
    rewrite Pr [mu_not].
    cut ->: Pr[Game(A).game(false) @ &m : true] = 1%r.
      byphoare (_:true) => //.
      by apply (Gamegame_lossless A).
    by smt.
  qed.

  (** Negligeble arithmetic value *)
  op epsilon: real.

  (** Probability of winning the game is negligeble *)
  axiom ES_assumption :
    is_uniform dkey =>
    is_uniform dcodom =>
    exists (epsilon:real),
    forall (A<:Adv_t) &m,
    `|2%r * Pr[Game(A).main()@ &m:res] - 1%r| <= epsilon.

end ES.

(** 
  List variation of the entropy smoothing assumption 

  Inputs: list (array) of elements in codom_t
  Output: a boolean b, trying to guess if those elements are the image of the hash, or random elements
  
  This theory is a direct extension of the previous one to one dimension container type.
*)
theory ESn.
  type dom_t.
  type codom_t.
  type hkey_t.
  op ddom:dom_t distr.
  op dcodom:codom_t distr.
  op dkey:hkey_t distr.

  (** Maximum size of the list (array) *)
  op nmax: int.

  clone KeyedHash as H with
   type dom_t = dom_t,
   type codom_t = codom_t,
   type hkey_t = hkey_t,
   op dkey = dkey.

  (** In this variant, the adversary chooses the length of the list *) 
  module type Adv_t = {
    proc choose_n(): int
    proc solve(key: hkey_t, a:codom_t array): bool
  }.

  module Game (A:Adv_t) = {
    proc game(b:bool): bool = {
      var n:int;
      var key:hkey_t;
      var x:dom_t array;
      var y,z:codom_t array;
      var guess:bool;

      n = A.choose_n();
      n = (0 <= n <= nmax) ? n : 0;

      key = $H.dkey;
      x = $Darray.darray ddom n;
      y = $Darray.darray dcodom n;

      if (b)
       z = offun (fun k, H.hash key x.[k]) n;
      else
       z = y;
      
      guess = A.solve(key, z);
      
      return guess = b;
    }
    
    proc main(): bool = {
      var b, adv: bool;

      b = ${0,1};
      adv = game(b);
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)
  
  lemma Gamegame_lossless (A <: Adv_t) :
    islossless A.choose_n =>
    islossless A.solve =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless Game(A).game.
  proof.
    move => Achoose_n_ll Asolve_ll Hkey_ll ddom_ll dcodom_ll.
    proc => //. 
    seq 1 : true => //; first by call (_:true).
    seq 4 : true => //.
      by auto; progress; expect 3 by smt. 
    if.
    (*b*)
      seq 1 : true => //.
      wp; skip; smt.
      by call (_:true).
    (*!b*)
      seq 1 : true => //.
      wp; skip; smt.
      by call (_:true).
  qed.

  lemma Gamemain_lossless (A <: Adv_t) : 
    islossless A.choose_n =>
    islossless A.solve =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless Game(A).main.
  proof.
    move => Achoose_n_ll Asolve_ll Hkey_ll ddom_ll dcodom_ll.
    proc => //.
    seq 1 : true => //; first by rnd; skip; smt.
    call (_:true).
    seq 1 : true => //; first by call (_:true).
    seq 4 : true => //.
      by auto; progress; expect 3 by smt.
    if.
    (*b*)
      seq 1 : true => //.
      wp; skip; smt.
      by call (_:true).
    (*!b*)
      seq 1 : true => //.
      wp; skip; smt.
      by call (_:true).
    skip; smt.
  qed.

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)
  
  (** Conditional probability expansion *)
  lemma Game_xpnd &m (A<:Adv_t):
    Pr[Game(A).main()  @ &m: res]
    = 1%r/2%r * (Pr[Game(A).game(true)  @ &m: res]
      + Pr[Game(A).game(false)  @ &m: res]).
  proof.
    pose p1 := Pr[Game(A).game(true) @ &m : res].
    pose p2 := Pr[Game(A).game(false) @ &m : res].
    byphoare (_: (glob A) = (glob A){m} ==> _) => //.
      proc => //.
      seq 1: b (1%r/2%r) p1 (1%r/2%r) p2 ((glob A) = (glob A){m}); trivial.
        by auto.
        by rnd; skip; smt.
        call (_: (glob A) = (glob A){m} /\ b ==> res)=> //.
          rewrite /p1.
          bypr=> &m' [eqA] b'.
          byequiv (_: ={glob A,b} /\ b{1} ==> ={res})=> //.
            by sim.
            by rewrite eqA b'.
        by rnd; skip; smt.
        call (_: (glob A) = (glob A){m} /\ !b ==> res)=> //.
          rewrite /p2.
          bypr=> &m' [eqA] b'.
          byequiv (_: ={glob A,b} /\ !b{1} ==> ={res})=> //.
          by sim.
          by move: b'; rewrite -neqF eqA=> ->.
        by smt.
  qed.

  (** Advantage definition *)
  lemma Game_adv &m (A<:Adv_t):
    is_lossless dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless A.choose_n =>
    islossless A.solve =>
    2%r * Pr[Game(A).main()  @ &m: res] - 1%r
    = Pr[Game(A).game(true)  @ &m: res]
      - Pr[Game(A).game(false)  @ &m: !res].
  proof.
    move => H1 H2 H3 Ainit_ll Asolve_ll.
    rewrite (Game_xpnd &m A).
    rewrite Pr [mu_not].
    cut ->: Pr[Game(A).game(false) @ &m : true] = 1%r.
      byphoare (_:true) => //.
      by apply (Gamegame_lossless A).
    by smt.
  qed.

  op epsilon: real.

  axiom ES_assumption:
    is_uniform dkey =>
    is_uniform dcodom =>
    exists (epsilon:real),
    forall (A<:Adv_t) &m,
    `|2%r * Pr[Game(A).main()@ &m:res] - 1%r| <= epsilon.

end ESn.
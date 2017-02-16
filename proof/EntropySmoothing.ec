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

  (**********************)
  (** ESnmax assumption *)
  (**********************)
  
  (** Maximum size of the list (array) *)
  const nmax:int.
  axiom nmax_pos: 0 < nmax.
  
  (** In this variant, the adversary chooses the length of the list *) 
  module type ESnmaxAdv_t = {
    proc init(): unit
    proc solve(key: hkey_t, a:codom_t array): bool
  }.

  module ESnmaxGame (A:ESnmaxAdv_t) = {
    proc game(b:bool): bool = {
      var n:int;
      var key:hkey_t;
      var x:dom_t array;
      var y,z:codom_t array;
      var guess:bool;

      A.init();

      key = $H.dkey;
      x = $Darray.darray ddom nmax;
      y = $Darray.darray dcodom nmax;

      if (b)
       z = offun (fun k, H.hash key x.[k]) nmax;
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
  
  lemma ESnmaxGamegame_lossless (A <: ESnmaxAdv_t) :
    islossless A.init =>
    islossless A.solve =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless ESnmaxGame(A).game.
  proof.
    move => Ainit_ll Asolve_ll Hkey_ll ddom_ll dcodom_ll.
    proc => //. 
    seq 1 : true => //; first by call (_:true).
    seq 3 : true => //.
      by auto; progress; expect 3 by smt. 
    if.
    (*b*)
      seq 1 : true => //.
      by wp; skip. 
      by call (_:true).
    (*!b*)
      seq 1 : true => //.
      by wp; skip.
      by call (_:true).
  qed.

  lemma ESnmaxGamemain_lossless (A <: ESnmaxAdv_t) : 
    islossless A.init =>
    islossless A.solve =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless ESnmaxGame(A).main.
  proof.
    move => Ainit_ll Asolve_ll Hkey_ll ddom_ll dcodom_ll.
    proc => //.
    seq 1 : true => //; first by rnd; skip; smt.
    call (_:true).
    seq 1 : true => //; first by call (_:true).
    seq 3 : true => //.
      by auto; progress; expect 3 by smt.
    if.
    (*b*)
      seq 1 : true => //.
      by wp; skip.
      by call (_:true).
    (*!b*)
      seq 1 : true => //.
      by wp; skip.
      by call (_:true).
    skip; smt.
  qed.

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)
  
  (** Conditional probability expansion *)
  lemma ESnmaxGame_xpnd &m (A<:ESnmaxAdv_t):
    Pr[ESnmaxGame(A).main()  @ &m: res]
    = 1%r/2%r * (Pr[ESnmaxGame(A).game(true)  @ &m: res]
      + Pr[ESnmaxGame(A).game(false)  @ &m: res]).
  proof.
    pose p1 := Pr[ESnmaxGame(A).game(true) @ &m : res].
    pose p2 := Pr[ESnmaxGame(A).game(false) @ &m : res].
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
  lemma ESnmaxGame_adv &m (A<:ESnmaxAdv_t):
    is_lossless dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless A.init =>
    islossless A.solve =>
    2%r * Pr[ESnmaxGame(A).main()  @ &m: res] - 1%r
    = Pr[ESnmaxGame(A).game(true)  @ &m: res]
      - Pr[ESnmaxGame(A).game(false)  @ &m: !res].
  proof.
    move => H1 H2 H3 Ainit_ll Asolve_ll.
    rewrite (ESnmaxGame_xpnd &m A).
    rewrite Pr [mu_not].
    cut ->: Pr[ESnmaxGame(A).game(false) @ &m : true] = 1%r.
      byphoare (_:true) => //.
      by apply (ESnmaxGamegame_lossless A).
    by smt.
  qed.

  (*******************)
  (* Reduction to ES *)
  (*******************)

  require Hybrid.

  clone Hybrid as Hy with
    type input <- hkey_t,
    type output <- codom_t,
    type inleaks <- unit,
    type outleaks <- unit,
    type outputA <- bool,
    op q <- nmax.
    
  (*module K = { var x: dom_t }.*)

  module ESl = {
    proc orcl (k:hkey_t) : codom_t = {
      var y : codom_t;
      var x : dom_t;

      x = $ddom;
      y = H.hash k x;
      
      return y;
    }
  }.
    
  module ESr = {
    proc orcl (k:hkey_t) : codom_t = {
      var y: codom_t;
      
      y = $dcodom;

      return y;
    }
  }.

  module ESb : Hy.Orclb = {
    proc leaks () : unit = {       
    }
    proc orclL = ESl.orcl
    proc orclR = ESr.orcl
  }.

  lemma islossless_leaks : islossless ESb.leaks.
  proof. by proc. qed.

  lemma islossless_orcl1 :  is_lossless ddom => islossless ESb.orclL.
  proof. progress;proc;auto;progress. qed.

  lemma islossless_orcl2 : is_lossless dcodom => islossless ESb.orclR.
  proof. progress;proc;auto;progress. qed.

  clone DArrayWhile as L1 with 
    type t<-codom_t.

  clone DArrayWhile2 as L2 with 
    type t1<-dom_t,
    type t2<-dom_t,
    type t<-codom_t.

  section.

    (** A specific instance of the DDH.Game is obtained when we restrict Ln/Rn to
    a single oracle call (through the H.B(-) adversary construction) *)
    module AdvES(A:ESnmaxAdv_t) : Adv_t = {
      var l0: int

      proc init() : unit = {
        A.init();
        l0 = $[0..nmax-1];
      }
      
      proc solve(key:hkey_t, x:codom_t): bool = {
        var z: codom_t array;
        var inp : dom_t;
        var y: codom_t;
        var b': bool;
        var i:int;
        
        i = 0;
        
        z = offun (fun k, x) nmax; (* just a default value *)

        while (i<nmax) {
          if (l0 < i) {
            inp = $ddom;
            z.[i] = H.hash key inp;
          }
          else {
            if (l0=i) {
              z.[i] = x;
            }
            else {
             y = $dcodom;
             z.[i] = y;
            }
          }
          i = i+1;
        }
        b' = A.solve(key, z);
        return b';
      }
    }.

    lemma AdvES_init_ll (A<:ESnmaxAdv_t):
      islossless A.init => islossless AdvES(A).init.
    proof.
      move=> H; proc; rnd; call (_:true) => //.
      skip. progress. 
      rewrite DInterval.mu_dinter List.size_filter List.count_predT List.Range.size_range ?max_ler; first by smt.
      by smt. 
    qed.

    lemma AdvES_solve_ll (A<:ESnmaxAdv_t):
      is_lossless dkey =>
      is_lossless ddom =>
      is_lossless dcodom =>
      islossless A.solve => islossless AdvES(A).solve.
    proof.
      progress; proc. 
      call (_:true) => //.
      while (i<=nmax) (nmax-i).
        move=> z.
        if.
          by wp; rnd; skip; progress; smt.
          if.
            by wp; skip; progress; smt.
            by wp; rnd; skip; progress; smt.
          by wp; skip; progress; smt.
    qed.

(* adversary attacking ESnmax (obs: does not have access to the state of
 the modules used in the hybrid argument)
*)
declare module Adv_ESnmax : ESnmaxAdv_t {AdvES, Hy.Count, Hy.HybOrcl}.

axiom Adv_ESnmax_init_ll: islossless Adv_ESnmax.init.

axiom Adv_ESnmax_solve_ll: islossless Adv_ESnmax.solve.

(* the functor ToAdv allow us to view Adv_ESnmax.Game as instaces of Ln/Rn games
 used by the generic Hybrid argument *)
local module ToAdv(Ob: Hy.Orclb, O:Hy.Orcl) = {
  proc main() : bool = {
    var key: hkey_t;
    var z: codom_t array;
    var dummy : codom_t;
    var x : dom_t array;
    var i: int;
    var b': bool;

    Adv_ESnmax.init();

    Ob.leaks();
    key = $dkey;  

    dummy = $dcodom;
    z = offun (fun k, dummy) nmax; (* just a default value *)
    i = 0;
    while (i < nmax) {
      z.[i] = O.orcl(key);
      i = i+1;
      }
    b' = Adv_ESnmax.solve(key, z);
    return b';
  }
}.

(** FIRST PART OF HYBRID *)
(** EQUIVALENCE WITH ESnmax *)

require import DProd.
local equiv ESn_Ln :
 ESnmaxGame(Adv_ESnmax).game ~ Hy.Ln(ESb, ToAdv).main :
 is_lossless dcodom /\ is_lossless ddom /\ b{1} /\ ={glob Adv_ESnmax} ==> ={res} /\ Hy.Count.c{2} <= nmax.
proof.
proc.
inline ESnmaxGame(Adv_ESnmax).game Hy.Count.init ToAdv(ESb, Hy.OrclCount(Hy.L(ESb))).main
 ESb.leaks Hy.OrclCount(Hy.L(ESb)).orcl Hy.L(ESb).orcl ESb.orclL.
  wp; call (_: is_lossless dcodom /\ is_lossless ddom /\ ={glob Adv_ESnmax,key,a} ==> ={res}); first by proc true.
rcondt {1} 5.
 move => &1; rnd; rnd; rnd. 
 by call (_: true); skip; trivial.
simplify.
swap{1} 4-1.
  seq 3 3: (is_lossless dcodom /\ is_lossless ddom /\ b{1} /\ ={glob Adv_ESnmax,key} /\ Hy.Count.c{2} = 0).
  rnd{1}; rnd; auto; call (_: true); wp; skip; smt.
transitivity {1} {
  z = L2.M.gen2(nmax,ddom,ddom,(fun a b, H.hash key a));
 }
 ( ={glob Adv_ESnmax, key} /\ is_lossless dcodom /\ is_lossless ddom /\ b{1} ==> is_lossless dcodom /\ is_lossless ddom /\ ={glob Adv_ESnmax, z, key} /\ b{1})
 ( ={glob Adv_ESnmax, key} /\ is_lossless dcodom /\ is_lossless ddom /\ Hy.Count.c{2}=0
  ==> ={glob Adv_ESnmax, key, z} /\ is_lossless dcodom /\ is_lossless ddom /\ Hy.Count.c{2} <= nmax).
    by progress; exists (glob Adv_ESnmax){2} key{2}; trivial.
  by progress; smt.
inline L2.M.gen2. wp. rnd{2}. rnd. wp. skip. progress. smt. 
cut Hnmax: 0 <= nmax by smt.
transitivity {2} {
  z = L2.M.gen1(nmax,ddom,ddom,(fun a b, H.hash key a),dummy);
 }
 ( ={glob Adv_ESnmax,key} /\ is_lossless dcodom /\ is_lossless ddom ==> ={glob Adv_ESnmax, key, z} /\ is_lossless dcodom /\ is_lossless ddom)
 ( ={glob Adv_ESnmax, key} /\ Hy.Count.c{2}=0 /\ is_lossless dcodom /\ is_lossless ddom
  ==> ={glob Adv_ESnmax, key, z} /\ is_lossless dcodom /\ is_lossless ddom /\ Hy.Count.c{2} <= nmax).
   by progress; exists (glob Adv_ESnmax){2} key{2}; trivial.
  by progress.
 symmetry.
 by call L2.darray2_loop_equiv.
inline L2.M.gen1. 
wp.
while (is_lossless dcodom /\ is_lossless ddom /\ ={key} /\ len{1}=nmax /\ i0{1} = i{2} /\ Hy.Count.c{2}=i{2} /\ i{2} <= nmax /\ f{1}=(fun a b, H.hash key{1} a) /\ d1{1} = ddom /\ d2{1} = ddom /\ size z0{1} = size z{2} /\ size z0{1} = nmax /\ (forall k, 0 <= k < i{2} => z0{1}.[k]=z{2}.[k])).
 inline Hy.Count.incr. wp. rnd{1}; rnd.
auto; progress. idtac=>/#. idtac=>/#. by rewrite !size_set. by rewrite !size_set. rewrite !get_set => /#. 
wp. rnd{2}. skip. progress. smt. smt. smt. smt. 
apply arrayP; split; first by smt.
smt. 
qed.

local lemma ESn_Ln_pr &m:
    is_lossless dcodom => is_lossless ddom =>
 Pr[ ESnmaxGame(Adv_ESnmax).game(true) @ &m : res]
 = Pr[Hy.Ln(ESb, ToAdv).main() @ &m : res /\ Hy.Count.c <= nmax].
proof. by progress; byequiv ESn_Ln. qed.

local equiv ESn_Rn:
 ESnmaxGame(Adv_ESnmax).game ~ Hy.Rn(ESb, ToAdv).main :
 is_lossless dcodom /\ is_lossless ddom /\ !b{1} /\ ={glob Adv_ESnmax} ==> res{1}=!res{2} /\ Hy.Count.c{2} <= nmax. 
proof.
proc.
inline ESnmaxGame(Adv_ESnmax).game Hy.Count.init ToAdv(ESb, Hy.OrclCount(Hy.R(ESb))).main
   ESb.leaks Hy.OrclCount(Hy.R(ESb)).orcl Hy.R(ESb).orcl ESb.orclR.
wp; call (_: is_lossless dcodom /\ is_lossless ddom /\ ={glob Adv_ESnmax,key,a} ==> ={res}); first by proc true.
rcondf {1} 5.
 move => &1; rnd; rnd; rnd. 
 by wp; call (_: true); skip; trivial.
simplify.
seq 3 4: (is_lossless dcodom /\ is_lossless ddom /\ !b{1} /\ ={glob Adv_ESnmax,key} /\ Hy.Count.c{2} = 0).
 rnd{1}. rnd{2}. rnd. call (_: true). wp. skip. progress. smt. smt. smt.

print L1.M.
transitivity {1} {
  z = L1.M.gen2(nmax,dcodom);
 }
 ( ={glob Adv_ESnmax, key} /\ is_lossless dcodom /\ is_lossless ddom /\ !b{1} ==> is_lossless dcodom /\ is_lossless ddom /\ ={glob Adv_ESnmax, z, key} /\ !b{1})
 ( ={glob Adv_ESnmax, key} /\ is_lossless dcodom /\ is_lossless ddom /\ Hy.Count.c{2}=0
  ==> ={glob Adv_ESnmax, key, z} /\ is_lossless dcodom /\ is_lossless ddom /\ Hy.Count.c{2} <= nmax).
    by progress; exists (glob Adv_ESnmax){2} key{2}; trivial.
  by progress; smt.
inline L1.M.gen2. wp. rnd. wp. skip. progress.  
cut Hnmax: 0 <= nmax by smt.
print L1.M.
transitivity {2} {
  z = L1.M.gen1(nmax,dcodom,dummy);
 }
 ( ={glob Adv_ESnmax,key} /\ is_lossless dcodom /\ is_lossless ddom ==> ={glob Adv_ESnmax, key, z} /\ is_lossless dcodom /\ is_lossless ddom)
 ( ={glob Adv_ESnmax, key} /\ Hy.Count.c{2}=0 /\ is_lossless dcodom /\ is_lossless ddom
  ==> ={glob Adv_ESnmax, key, z} /\ is_lossless dcodom /\ is_lossless ddom /\ Hy.Count.c{2} <= nmax).
   by progress; exists (glob Adv_ESnmax){2} key{2}; trivial.
  by progress.
 symmetry.
 by call L1.darray_loop_equiv.
inline L1.M.gen1. 
wp.

while (is_lossless dcodom /\ is_lossless ddom /\ ={key} /\ len{1}=nmax /\ i0{1} = i{2} /\ Hy.Count.c{2}=i{2} /\ i{2} <= nmax /\ d{1} = dcodom /\ size xs{1} = size z{2} /\ size xs{1} = nmax /\ (forall k, 0 <= k < i{2} => xs{1}.[k]=z{2}.[k])).
 inline Hy.Count.incr. wp. rnd.
auto; progress. idtac=>/#. by rewrite !size_set. by rewrite !size_set. rewrite !get_set => /#. 
wp. skip. progress. smt. smt. smt.  
apply arrayP; split; first by smt.
smt. 
qed.

local lemma ESn_Rn_pr &m:
    is_lossless dcodom => is_lossless ddom =>
 Pr[ ESnmaxGame(Adv_ESnmax).game(false) @ &m : !res]
 = Pr[Hy.Rn(ESb, ToAdv).main() @ &m : res /\ Hy.Count.c <= nmax]
by progress; byequiv ESn_Rn.

(** SECOND PART OF HYBRID *)
(** EQUIVALENCE WITH ES *)
 
local equiv ES_L1:
 Game(AdvES(Adv_ESnmax)).game ~ Hy.Ln(ESb, Hy.HybGame(ToAdv)).main :
 is_lossless ddom /\ b{1} /\ ={glob Adv_ESnmax} ==> ={res} /\ Hy.HybOrcl.l{2} <= nmax /\ Hy.Count.c{2} <= 1.
proof.
proc.
inline Hy.HybGame(ToAdv, ESb, Hy.OrclCount(Hy.L(ESb))).main
 Hy.HybGame(ToAdv, ESb, Hy.OrclCount(Hy.L(ESb))).A.main
 AdvES(Adv_ESnmax).init AdvES(Adv_ESnmax).solve Hy.HybOrcl(ESb, Hy.OrclCount(Hy.L(ESb))).orcl
   ESb.orclL ESb.orclR Hy.OrclCount(Hy.L(ESb)).orcl ESb.leaks.
rcondt{1} 6. auto. call (_ : true). auto.
wp; call (_: is_lossless ddom /\ ={glob Adv_ESnmax, key, a} ==> ={res}); first by proc true.
swap{1} 4-1. swap{1} 6-2.
seq 4 5: (is_lossless ddom /\ b{1} /\ AdvES.l0{1}=Hy.HybOrcl.l0{2} /\
          0 <= Hy.HybOrcl.l0{2} < nmax /\
          Hy.HybOrcl.l{2}=0 /\ Hy.Count.c{2} = 0 /\ k{1} = key{2} /\ ={glob Adv_ESnmax,key}).
 wp; rnd; seq 2 4: (is_lossless ddom /\ b{1} /\ Hy.Count.c{2}=0 /\ AdvES.l0{1}=Hy.HybOrcl.l0{2} /\
                0 <= Hy.HybOrcl.l0{2} < nmax /\ Hy.HybOrcl.l{2}=0 /\
                ={glob Adv_ESnmax}).
 swap {1} 2 -1.
 call (_: is_lossless ddom /\ ={glob Adv_ESnmax} ==> ={glob Adv_ESnmax, res}); first by proc true.
  inline Hy.Count.init; wp; rnd; wp.
  by skip; progress; smt. 
 done.
              
splitwhile{1} 6: (i < AdvES.l0).
splitwhile{2} 4: (i < Hy.HybOrcl.l0).

splitwhile{1} 7 : (i = AdvES.l0).
splitwhile{2} 5: (Hy.HybOrcl.l0 = Hy.HybOrcl.l).

unroll{1} 7.
unroll{2} 5.

rcondt{1} 7. move => &m. while (0 <= i <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondt{2} 5. move => &m. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. idtac=>/#.

rcondf{1} 7. move => &m. while (0 <= i <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondf{2} 6. move => &m. wp. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. 

rcondt{1} 7. move => &m. while (0 <= i <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondt{2} 6. move => &m. wp. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. 

rcondf{1} 9. move => &m. wp. while (0 <= i <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondf{2} 16. move => &m. inline Hy.Count.incr. auto. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. 

alias{2} 8 with v. swap{2} 8 -7.

while (is_lossless ddom /\ ={glob Adv_ESnmax, i, key} /\ b{1} /\
      Hy.HybOrcl.l0{2} < i{2} /\ size z{1} = size z{2} /\ size z{1} = nmax /\
      AdvES.l0{1} = Hy.HybOrcl.l0{2} /\
      x0{1} = H.hash k{1} x{1} /\ Hy.HybOrcl.l{2}=i{2} /\
      i{2}<=nmax /\ Hy.Count.c{2}<=1 /\ (forall k, 0 <= k < i{2} => z{1}.[k] = z{2}.[k])).

 rcondt {1} 1; first by move=> &m; skip; progress.  
 rcondt {2} 2; first by move=> &m; wp; skip; progress. 
 wp. rnd. wp. auto; progress. idtac=>/#. by rewrite !size_set. by rewrite size_set. idtac=>/#. rewrite !get_set. idtac=>/#. idtac=>/#. idtac=>/#.

inline Hy.Count.incr.
wp.

while (is_lossless ddom /\ ={glob Adv_ESnmax, i, key} /\ b{1} /\
            0 <= Hy.HybOrcl.l0{2} < nmax /\ size z{1} = size z{2} /\ size z{1} = nmax /\
            AdvES.l0{1} = Hy.HybOrcl.l0{2} /\
            x0{1} = H.hash k{1} x{1} /\ Hy.HybOrcl.l{2}=i{2} /\
  0<=i{2}<=Hy.HybOrcl.l0{2} /\ Hy.Count.c{2}=0 /\ (forall k, 0 <= k < i{2} => z{1}.[k] = z{2}.[k])).
  rcondf {2} 2; first by move => &m; wp; skip; progress; smt.
  rcondf {2} 2; first by move => &m; wp; skip; progress; smt.
rcondf{1} 1; first by move => &m; skip; progress; smt.
rcondf{1} 1; first by move => &m; skip; progress; smt.

  wp. rnd. auto; progress. by rewrite !size_set. by rewrite size_set. idtac=>/#. idtac=>/#. rewrite !get_set => /#. 
wp. rnd. rnd. skip; progress. 
         smt. smt. smt. smt. by rewrite !size_set. by rewrite size_set. idtac=>/#. rewrite !get_set => /#.  rewrite arrayP; split; first by smt. move => i i_size. idtac=>/#. idtac=>/#.
qed.              

local lemma ES_L1_pr &m:
    is_lossless ddom =>
 Pr[Game(AdvES(Adv_ESnmax)).game(true) @ &m : res]
 = Pr[Hy.Ln(ESb, Hy.HybGame(ToAdv)).main() @ &m : (res /\ Hy.HybOrcl.l <= nmax) /\ Hy.Count.c <= 1]
 by progress;byequiv ES_L1.

local equiv ES_R1:
 Game(AdvES(Adv_ESnmax)).game ~ Hy.Rn(ESb, Hy.HybGame(ToAdv)).main :
 is_lossless ddom /\ is_lossless dcodom /\ !b{1} /\ ={glob Adv_ESnmax} ==> res{1}=!res{2} /\ Hy.HybOrcl.l{2} <= nmax /\ Hy.Count.c{2} <= 1.
proof.
proc.
inline Hy.HybGame(ToAdv, ESb, Hy.OrclCount(Hy.R(ESb))).main
 Hy.HybGame(ToAdv, ESb, Hy.OrclCount(Hy.R(ESb))).A.main
 AdvES(Adv_ESnmax).init AdvES(Adv_ESnmax).solve Hy.HybOrcl(ESb, Hy.OrclCount(Hy.R(ESb))).orcl
   ESb.orclL ESb.orclR Hy.OrclCount(Hy.R(ESb)).orcl ESb.leaks.
rcondf{1} 6. auto. call (_ : true). auto.
wp; call (_: is_lossless ddom /\ is_lossless dcodom /\ ={glob Adv_ESnmax, key, a} ==> ={res}); first by proc true.

swap {2} 4-3.

seq 4 5: (is_lossless ddom /\ is_lossless dcodom /\ !b{1} /\ AdvES.l0{1}=Hy.HybOrcl.l0{2} /\
          0 <= Hy.HybOrcl.l0{2} < nmax /\
          Hy.HybOrcl.l{2}=0 /\ Hy.Count.c{2} = 0 /\ k{1} = key{2} /\ ={glob Adv_ESnmax}).
rnd. rnd{1}. wp. rnd. inline Hy.Count.init. wp. 
call (_: is_lossless ddom /\ ={glob Adv_ESnmax} ==> ={glob Adv_ESnmax, res}); first by proc true.
skip; progress. smt. smt. smt. smt. 
              
splitwhile{1} 6: (i0 < AdvES.l0).
splitwhile{2} 4: (i < Hy.HybOrcl.l0).

splitwhile{1} 7 : (i0 = AdvES.l0).
splitwhile{2} 5: (Hy.HybOrcl.l0 = Hy.HybOrcl.l).

unroll{1} 7.
unroll{2} 5.

rcondt{1} 7. move => &m. while (0 <= i0 <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.  
rcondt{2} 5. move => &m. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. idtac=>/#.

rcondf{1} 7. move => &m. while (0 <= i0 <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondf{2} 6. move => &m. wp. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. 

rcondt{1} 7. move => &m. while (0 <= i0 <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondt{2} 6. move => &m. wp. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. 

rcondf{1} 9. move => &m. wp. while (0 <= i0 <= AdvES.l0). if. auto. smt. if. auto. auto. smt. auto. smt.
rcondf{2} 15. move => &m. inline Hy.Count.incr. auto. while (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax). seq 1 : (0 <= i <= Hy.HybOrcl.l0 /\ i = Hy.HybOrcl.l /\ 0 <= Hy.HybOrcl.l0 < nmax /\ i < nmax /\ i < Hy.HybOrcl.l0 /\ m = key). auto. if. auto. progress. idtac=>/#. idtac=>/#. if. inline Hy.Count.incr. auto. auto. progress. idtac=>/#. idtac=>/#. auto. progress. idtac=>/#. 

alias{2} 8 with v. swap{2} 8 -7.

while (is_lossless ddom /\ is_lossless dcodom /\ ={glob Adv_ESnmax} /\ !b{1} /\ i0{1} = i{2} /\
      Hy.HybOrcl.l0{2} < i{2} /\ size z0{1} = size z{2} /\ size z0{1} = nmax /\
      AdvES.l0{1} = Hy.HybOrcl.l0{2} /\
      Hy.HybOrcl.l{2}=i{2} /\ key0{1} = key{2} /\
      i{2}<=nmax /\ Hy.Count.c{2}<=1 /\ (forall k, 0 <= k < i{2} => z0{1}.[k] = z{2}.[k])).

 rcondt {1} 1; first by move=> &m; skip; progress.  
 rcondt {2} 2; first by move=> &m; wp; skip; progress. 
 wp. rnd. wp. auto; progress. idtac=>/#. by rewrite !size_set. by rewrite !size_set. idtac=>/#. rewrite !get_set. idtac=>/#. idtac=>/#. idtac=>/#.

inline Hy.Count.incr. wp.

while (is_lossless ddom /\ is_lossless dcodom /\ ={glob Adv_ESnmax} /\ !b{1} /\ i0{1} = i{2} /\
            0 <= Hy.HybOrcl.l0{2} < nmax /\ size z0{1} = size z{2} /\ size z0{1} = nmax /\
            AdvES.l0{1} = Hy.HybOrcl.l0{2} /\
            Hy.HybOrcl.l{2}=i{2} /\ key0{1} = key{2} /\
  0<=i{2}<=Hy.HybOrcl.l0{2} /\ Hy.Count.c{2}=0 /\ (forall k, 0 <= k < i{2} => z0{1}.[k] = z{2}.[k])).
  rcondf {2} 2; first by move => &m; wp; skip; progress => /#. 
  rcondf {2} 2; first by move => &m; wp; skip; progress => /#. 
rcondf{1} 1; first by move => &m; skip; progress => /#. 
rcondf{1} 1; first by move => &m; skip; progress => /#. 

wp. rnd. auto; progress. by rewrite !size_set. by rewrite size_set. idtac=>/#. idtac=>/#. rewrite !get_set => /#. 
wp. rnd{2}. rnd. auto; progress. idtac=>/#. by rewrite !size_offun. by rewrite size_offun max_ler => /#. idtac=>/#. idtac=>/#. by rewrite !size_set. by rewrite size_set. idtac=>/#. rewrite !get_set => /#. rewrite arrayP => /#. idtac=>/#. 
qed.

local lemma ES_R1_pr &m:
    is_lossless ddom =>
    is_lossless dcodom =>
 Pr[Game(AdvES(Adv_ESnmax)).game(false) @ &m : !res]
 = Pr[Hy.Rn(ESb, Hy.HybGame(ToAdv)).main() @ &m : (res /\ Hy.HybOrcl.l <= nmax) /\ Hy.Count.c <= 1]
 by progress;byequiv ES_R1.
 
(* The generic hybrid argument... *)
 local lemma hyb &m:
     is_lossless ddom =>
     is_lossless dcodom =>
     is_lossless dkey =>
 Pr[Hy.Ln(ESb, Hy.HybGame(ToAdv)).main() @ &m : (res /\ Hy.HybOrcl.l <= nmax) /\ Hy.Count.c <= 1 ] -
 Pr[Hy.Rn(ESb, Hy.HybGame(ToAdv)).main() @ &m : (res /\ Hy.HybOrcl.l <= nmax) /\ Hy.Count.c <= 1 ] = 
 1%r / nmax%r *
  (Pr[Hy.Ln(ESb, ToAdv).main() @ &m : (res /\ Hy.Count.c <= nmax) ] -
   Pr[Hy.Rn(ESb, ToAdv).main() @ &m : (res /\ Hy.Count.c <= nmax) ]).
proof. 
move => ddom_ll dcodom_ll dkey_ll. apply (Hy.Hybrid (<:ESb) (<:ToAdv) _ _ _ _ &m 
       (fun (ga:glob ToAdv) (gb:glob ESb) (c:int) (r:bool), r)).
 by apply islossless_leaks.
 by apply islossless_orcl1.
 by apply islossless_orcl2.
 move => Ob LR orcl_ll leaks_ll orcl1_ll orcl2_ll.
 proc.
 call (_:true); first by apply Adv_ESnmax_solve_ll.
 while true (nmax-i).
  move=> z; wp; call (_:true) => //; skip; progress; smt.
 wp; do 2!rnd; call (_:true) => //.
 call (_:true); first by apply Adv_ESnmax_init_ll.
 skip; progress; smt.
qed.

lemma ESnmax_adv_bound:
    is_lossless ddom =>
     is_lossless dcodom =>
    is_lossless dkey =>
    forall &m epsilon,
 `| 2%r * Pr[ Game(AdvES(Adv_ESnmax)).main() @ &m: res ] - 1%r| <= epsilon =>
 `| 2%r * Pr[ ESnmaxGame(Adv_ESnmax).main() @ &m: res ] - 1%r| <= nmax%r * epsilon.
proof.
move => ddom_ll dcodom_ll dkey_ll &m epsilon.
move: Adv_ESnmax_init_ll Adv_ESnmax_solve_ll => H1_ll H2_ll.
rewrite (Game_adv &m (AdvES(Adv_ESnmax))) //. 
  proc. rnd. call H1_ll. skip; progress; smt. 
 proc. call Adv_ESnmax_solve_ll. while true (nmax - i). move => z. if. auto. smt. if. auto. smt. auto. smt. auto. smt. 
rewrite (ESnmaxGame_adv &m Adv_ESnmax) //.
rewrite (ES_L1_pr &m) // (ES_R1_pr &m) // (ESn_Ln_pr &m) // (ESn_Rn_pr &m) // (hyb &m) //.
move: (Pr[Hy.Ln(ESb, ToAdv).main() @ &m : res /\ Hy.Count.c <= nmax] -
       Pr[Hy.Rn(ESb, ToAdv).main() @ &m : res /\ Hy.Count.c <= nmax]) => adv.
cut Hpos: 0%r <= 1%r / nmax%r by smt.
cut H1: Real.zero <= nmax%r by smt. 
cut ->: `|(1%r / nmax%r) * adv| = 1%r / nmax%r * `|adv| by smt tmo=10. 
cut H2: 0%r <= `| adv| by smt.
move=> H. smt.
qed.

end section.



(** 
  List variation of the entropy smoothing assumption 

  Inputs: list (array) of elements in codom_t
  Output: a boolean b, trying to guess if those elements are the image of the hash, or random elements
  
  This theory is a direct extension of the previous one to one dimension container type.
*)


  (*clone KeyedHash as H with
   type dom_t = ES.dom_t,
   type codom_t = ES.codom_t,
   type hkey_t = ES.hkey_t,
   op dkey = ES.dkey.*)

  (** In this variant, the adversary chooses the length of the list *) 
  module type ESnAdv_t = {
    proc choose_n(): int
    proc solve(key: hkey_t, a:codom_t array): bool
  }.

  module ESnGame (A:ESnAdv_t) = {
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
  
  lemma ESnGamegame_lossless (A <: ESnAdv_t) :
    islossless A.choose_n =>
    islossless A.solve =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless ESnGame(A).game.
  proof.
    move => Achoose_n_ll Asolve_ll Hkey_ll ddom_ll dcodom_ll.
    proc => //. 
    seq 1 : true => //; first by call (_:true).
    seq 4 : true => //. 
      by auto; progress; expect 3 by smt tmo=10. 
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

  lemma ESnGamemain_lossless (A <: ESnAdv_t) : 
    islossless A.choose_n =>
    islossless A.solve =>
    is_lossless H.dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless ESnGame(A).main.
  proof.
    move => Achoose_n_ll Asolve_ll Hkey_ll ddom_ll dcodom_ll.
    proc => //.
    seq 1 : true => //; first by rnd; skip; smt.
    call (_:true).
    seq 1 : true => //; first by call (_:true).
    seq 4 : true => //.
      by auto; progress; expect 3 by smt tmo=10.
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
  lemma ESnGame_xpnd &m (A<:ESnAdv_t):
    Pr[ESnGame(A).main()  @ &m: res]
    = 1%r/2%r * (Pr[ESnGame(A).game(true)  @ &m: res]
      + Pr[ESnGame(A).game(false)  @ &m: res]).
  proof.
    pose p1 := Pr[ESnGame(A).game(true) @ &m : res].
    pose p2 := Pr[ESnGame(A).game(false) @ &m : res].
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
  lemma ESnGame_adv &m (A<:ESnAdv_t):
    is_lossless dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
    islossless A.choose_n =>
    islossless A.solve =>
    2%r * Pr[ESnGame(A).main()  @ &m: res] - 1%r
    = Pr[ESnGame(A).game(true)  @ &m: res]
      - Pr[ESnGame(A).game(false)  @ &m: !res].
  proof.
    move => H1 H2 H3 Ainit_ll Asolve_ll.
    rewrite (ESnGame_xpnd &m A).
    rewrite Pr [mu_not].
    cut ->: Pr[ESnGame(A).game(false) @ &m : true] = 1%r.
      byphoare (_:true) => //.
      by apply (ESnGamegame_lossless A).
    by smt.
  qed.
  
  module AESnmax (A: ESnAdv_t) : ESnmaxAdv_t = {
    var n: int

    proc init() : unit = {
      n = A.choose_n();
      n = (0 <= n <= nmax) ? n : 0;
    }

    proc solve(key:hkey_t, a : codom_t array) : bool = {
      var b': bool;
      var ndiff: int;
      var xx:codom_t array;

      (* truncate the arrays!!! ---  fill the difference... *)
      xx = take n a;

      b' = A.solve(key, xx);
      return b';
    }
  }.

import DProd.
clone DArrayTake as L3 with type t <- dom_t.
clone DArrayTake as L4 with type t <- codom_t.

equiv ESn_nmax (A <: ESnAdv_t {AESnmax}) :
 ESnGame(A).main ~ ESnmaxGame(AESnmax(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline ESnGame(A).game ESnmaxGame(AESnmax(A)).game
 AESnmax(A).init AESnmax(A).solve.
wp; call (_: ={glob A, key, a} ==> ={res}); first by proc true.

seq 5 5: (={b0, glob A,key} /\ 0 <= n{1} <= nmax /\ n{1}=AESnmax.n{2}).
 rnd; wp; call (_: ={glob A} ==> ={glob A, res}); first by proc true.
 by wp; rnd; skip; progress; smt.

transitivity {2} {
  x = $Darray.darray ddom nmax;
  x = take AESnmax.n x;
  y = $Darray.darray dcodom nmax;
  y = take AESnmax.n y;
  z = offun (fun k, 
        if b0 then H.hash key x.[k] else y.[k]) AESnmax.n;
  }
  ( ={glob A,b0,key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1}=AESnmax.n{2}
    ==> ={z,b0,key,glob A} )
  ( ={glob A,b0,key,AESnmax.n}  /\ 0 <= AESnmax.n{2} <= nmax 
    ==> ={b0,key,AESnmax.n,glob A} /\ z{1}=xx{2} /\ key0{2} = key{2}).
   progress.
   by exists (glob A){2} AESnmax.n{2} b0{2} key{2}; smt.
  by progress.
 wp 2 4.
 seq 1 2: (={glob A, b0, x, key} /\
           0 <= AESnmax.n{2} <= nmax /\ n{1}=AESnmax.n{2}).
  transitivity {1} {
   x = L3.M.gen1(n,ddom);
   }
   ( ={glob A, b0, key, n} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} ==> ={glob A, b0, key, x, n} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2})
   ( ={glob A, b0, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2}
      ==> ={glob A, b0, x, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} ).
     progress. by progress; exists (glob A){2} AESnmax.n{2} b0{2} key{2} AESnmax.n{2}; smt.
    by progress.
   by inline L3.M.gen1; wp; rnd; wp; skip; progress.
  transitivity {2} {
   x = L3.M.gen2(nmax,AESnmax.n,ddom);
   }
   ( ={glob A, b0, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2}
     ==> ={glob A, b0, x, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} )
   ( ={glob A, b0, key, AESnmax.n} ==> ={glob A, b0, x, key, AESnmax.n} ). 
     by progress; exists (glob A){2} AESnmax.n{2} b0{2} key{2}; smt.
    by progress.
   by call L3.darray_take_equiv.
  by inline L3.M.gen2; wp; rnd; wp; skip; progress; rewrite ?takeE. simplify.
 (*conseq (_: ={glob A, b0, x, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} ==> ={glob A, b0, x, key, y} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2}). progress. smt. first by progress.*)
 transitivity {1} {
  y = L4.M.gen1(n,dcodom);
  }
  ( ={glob A, b0, x, key, n} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} ==> ={glob A, b0, x, y, key, n} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} /\ size y{1} = n{1})
  ( ={glob A, b0, x, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2}
     ==> ={glob A, b0, x, y, key} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} ).
    by progress; exists (glob A){2} AESnmax.n{2} b0{2} key{2} AESnmax.n{2}
         x{2}; smt.
   progress. smt. 
  inline L4.M.gen1; wp; rnd; wp; skip; progress. smt.
 transitivity {2} {
  y = L4.M.gen2(nmax,AESnmax.n,dcodom);
  }
  ( ={glob A, b0, key, x} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2}
    ==> ={glob A, b0, key, x, y} /\ 0 <= AESnmax.n{2} <= nmax /\ n{1} = AESnmax.n{2} )
  ( ={glob A, b0, key, x, AESnmax.n} ==> ={glob A, b0, key, x, y, AESnmax.n} ). 
    by progress; exists (glob A){2} AESnmax.n{2} b0{2} key{2} x{2}; smt.
   by progress.
  by call L4.darray_take_equiv.
 by inline L4.M.gen2; wp; rnd; wp; skip; progress; rewrite ?takeE.

wp; rnd; wp; rnd.
skip; progress. 
 apply arrayP; split.
  rewrite ?size_offun // size_take //; first 2 by smt. 
 move=> k; rewrite size_offun // => _.
 rewrite offunifE // get_take //=; first by smt.
 rewrite get_take //=; first by smt.
 rewrite offunifE //=; first by smt.
apply arrayP; split.
 rewrite ?size_offun // size_take //; first 2 by smt.
move=> k; rewrite size_offun // => _. 
rewrite offunifE // get_take //=; first by smt. smt.
qed.

lemma ESn_nmax_pr &m (A<:ESnAdv_t {AESnmax}):
 Pr[ESnGame(A).main() @ &m : res]
 = Pr[ESnmaxGame(AESnmax(A)).main() @ &m : res] by byequiv (ESn_nmax A).

lemma ESn_adv_bound &m (A<:ESnAdv_t {AESnmax, Hy.Count, Hy.HybOrcl, AdvES}) epsilon:
    is_lossless dkey =>
    is_lossless ddom =>
    is_lossless dcodom =>
 islossless A.choose_n =>
 islossless A.solve =>
 `| 2%r * Pr[ Game(AdvES(AESnmax(A))).main() @ &m: res ] - 1%r| <= epsilon =>
 `| 2%r * Pr[ ESnGame(A).main() @ &m: res ] - 1%r| <= nmax%r * epsilon.
proof.
move=> dkey_ll ddom_ll dcodom_ll A_choose_ll A_solve_ll; rewrite (ESn_nmax_pr &m A).
apply (ESnmax_adv_bound (AESnmax(A)) _ _ _ _ _ &m); last 3 by assumption.
  by proc; wp; call A_choose_ll.
  by proc; call A_solve_ll; wp.
qed.
  
end ES.
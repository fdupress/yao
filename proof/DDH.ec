(** Decisional Diffie-Hellman problem *)
require import Bool.
require import Int.
require import IntExtra.
require import IntDiv.
require import Pair.
require import Real.
require import Distr.
require import DBool.

require import Array.
require import ArrayExt.

require import Prime_field.
require import Cyclic_group_prime.

(**
  Decision Diffie-Hellman problem.

  In this problem, an adversary is asked to distinguish
  between an exponentiation that results from the typical
  Diffie-Hellman setting (g^(x*y)) and an exponentiation
  with a truly random value (g^z) that has nothing to do
  with the Diffie-Hellman set up.
*)
theory DDH.

  (** Adversary *)
  (** 
    The adversary is the routine that breaks the DDH assumption.
    It starts by setting up the game and then, on input to three
    values of the cyclic group, it outputs a bit b', whether it was
    able to distinguish between g^(x*y) and g^z, with random z.
  *)
  module type Adv_t = {
    proc init(): unit
    proc solve(gx:group, gy:group, gz:group): bool
  }.

  (** DDH cryptographic game *)
  (**
    This game will use the adversary defined above (that attacks the security
    of the DDH assumption) to try to break the security of the scheme.

    The routine starts by initialising the adversary and then samples the
    values that will be used by the remain procedure. After, the adversary is
    given g^x and g^y (elements of the Diffie-Hellman set up) and another value
    that can be either g^(x*y) (that finishes the key exchange in Diffie-Hellman) 
    or g^z, being z a random value that has nothing to do with the scheme.
    The adversary is then asked to distinguish if it is in the presence of a 
    Diffie-Hellman key exchange value or a random value.
  *)
  module Game (A:Adv_t) = {
    proc game(b: bool): bool = {
      var x,y,z:gf_q;
      var b':bool;
      var gxy:group;

      A.init();
      x = $Dgf_q.dgf_q;
      y = $Dgf_q.dgf_q;
      z = $Dgf_q.dgf_q;
      gxy = if b then g^(x*y) else g^z;
      b' = A.solve(g ^ x, g ^ y, gxy);
      return b'=b;
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
    islossless Game(A).game.
   proof.  
     move => Ainit_ll Asolve_ll.
     proc => //.
     call (_:true); first by apply Asolve_ll.
     auto.
     call (_:true); first by apply Ainit_ll.
     by skip; smt.
  qed.

  lemma Gamemain_lossless (A <: Adv_t) :
    islossless A.init =>
    islossless A.solve =>
    islossless Game(A).main.
   proof.  
     move => Ainit_ll Asolve_ll.
     proc => //.
     seq 1 : true => //; first by auto;smt.
     call (_:true) => //. 
     call (_:true); first by apply Asolve_ll.
     auto.
     call (_:true); first by apply Ainit_ll.
     by skip; smt.
  qed.


  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)

  (**
    The advantage of an adversary against the DDH assumption 
    with respect to the games above is |2*Pr[adv = b] - 1|. The scheme is secure
    if the advantage is negligeble.

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
  lemma DDH_adv &m (A<:Adv_t):
    islossless A.init =>
    islossless A.solve =>
    2%r * Pr[Game(A).main()  @ &m: res] - 1%r
    = Pr[Game(A).game(true)  @ &m: res] 
      - Pr[Game(A).game(false)  @ &m: !res].
  proof.
    move=> Ainit_ll Asolve_ll.
    rewrite Pr [mu_not].
    pose p1:= Pr[Game(A).game(true) @ &m : res].
    pose p2:= Pr[Game(A).game(false) @ &m : res].
    cut ->: Pr[Game(A).game(false) @ &m : true] = 1%r.
      byphoare (_:true)=> //.
      by apply (Gamegame_lossless A); smt. 
    cut Hp1: phoare [Game(A).game: b /\ (glob A)=(glob A){m} ==> res] = p1.
      bypr=> &m' [b' gA]; rewrite /p1 b'.
      by byequiv (_: ={b, glob A} ==> ={res})=> //; first by sim.
    cut Hp2: phoare [Game(A).game: !b /\ (glob A)=(glob A){m} ==> res] = p2.
      bypr=> &m' ; rewrite -neqF; move => [b' gA]; rewrite /p2 b'.
      byequiv (_: ={b, glob A} ==> ={res})=> //; first by sim.
    cut Hp: phoare [Game(A).main: (glob A)=(glob A){m} ==> res] = ((p1+p2)/2%r).
    proc => //.
    seq 1: b (1%r / 2%r) p1 (1%r / 2%r) p2 ((glob A)=(glob A){m}).
      by auto.
      by rnd ((=) true); skip; smt.
      by call Hp1.
      by rnd ((=) false); skip; smt.
      by call Hp2.
      by smt.
    cut ->: Pr[Game(A).main() @ &m : res] = ((p1+p2)/2%r).
      by byphoare Hp.
    by smt.
  qed.

end DDH.

(** 
  List variation of the Decisional Diffie-Hellman problem (fixed size)

  Inputs: g^a and a list (array) of pairs (g^b1, g^c1), ..., (g^bn, g^cn)
  Output: a boolean b, trying to guess if ci = a * bi
*)
theory DDHnmax.

  const nmax:int.
  axiom nmax_pos: 0 < nmax.

  module type Adv_t = {
    proc init(): unit
    proc solve(gx:group, gyzs:(group*group) array): bool
  }.

  module Game (A:Adv_t) = {
    proc game(b:bool): bool = {
      var n: int;
      var x:gf_q;
      var y,z:gf_q array;
      var gyzs:(group*group) array;
      var guess:bool;

      A.init();

      x = $Dgf_q.dgf_q;
      y = $Darray.darray Dgf_q.dgf_q nmax;
      z = $Darray.darray Dgf_q.dgf_q nmax;

      if (b)
       gyzs = offun (fun k, (g^y.[k], g^(x*y.[k]))) nmax;
      else
       gyzs = offun (fun k, (g^y.[k], g^(z.[k]))) nmax;
 
      guess = A.solve(g^x, gyzs);

      return guess=b;
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
    islossless Game(A).game.
   proof.  
     move => Ainit_ll Asolve_ll.
     proc => //.
     call (_:true); first by apply Asolve_ll.
     auto.
     call (_:true); first by apply Ainit_ll.
     by skip; smt.
  qed.

  lemma Gamemain_lossless (A <: Adv_t) :
    islossless A.init =>
    islossless A.solve =>
    islossless Game(A).main.
   proof.  
     move => Ainit_ll Asolve_ll.
     proc => //.
     seq 1 : true => //; first by auto;smt.
     call (_:true) => //. 
     call (_:true); first by apply Asolve_ll.
     auto.
     call (_:true); first by apply Ainit_ll => //.
     by skip; smt.
  qed.

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)

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
  lemma DDH_adv &m (A<:Adv_t):
    islossless A.init =>
    islossless A.solve =>
    2%r * Pr[Game(A).main()  @ &m: res] - 1%r
    = Pr[Game(A).game(true)  @ &m: res] 
      - Pr[Game(A).game(false)  @ &m: !res].
  proof.
    move=> Ainit_ll Asolve_ll.
    rewrite Pr [mu_not].
    pose p1:= Pr[Game(A).game(true) @ &m : res].
    pose p2:= Pr[Game(A).game(false) @ &m : res].
    cut ->: Pr[Game(A).game(false) @ &m : true] = 1%r.
      byphoare (_:true)=> //.
      by apply (Gamegame_lossless A); smt. 
    cut Hp1: phoare [Game(A).game: b /\ (glob A)=(glob A){m} ==> res] = p1.
      bypr=> &m' [b' gA]; rewrite /p1 b'.
      by byequiv (_: ={b, glob A} ==> ={res})=> //; first by sim.
    cut Hp2: phoare [Game(A).game: !b /\ (glob A)=(glob A){m} ==> res] = p2.
      bypr=> &m' ; rewrite -neqF; move => [b' gA]; rewrite /p2 b'.
      byequiv (_: ={b, glob A} ==> ={res})=> //; first by sim.
    cut Hp: phoare [Game(A).main: (glob A)=(glob A){m} ==> res] = ((p1+p2)/2%r).
    proc => //.
    seq 1: b (1%r / 2%r) p1 (1%r / 2%r) p2 ((glob A)=(glob A){m}).
      by auto.
      by rnd ((=) true); skip; smt.
      by call Hp1.
      by rnd ((=) false); skip; smt.
      by call Hp2.
      by smt.
    cut ->: Pr[Game(A).main() @ &m : res] = ((p1+p2)/2%r).
      by byphoare Hp.
    by smt.
  qed.
  
  (********************)
  (* Reduction to DDH *)
  (********************)

  require Hybrid.

  clone Hybrid as H with
    type input <- unit,
    type output <- group * group,
    type inleaks <- unit,
    type outleaks <- group,
    type outputA <- bool,
    op q <- nmax.

  module K = { var x: gf_q }.

  module DDHl = {
    proc orcl (x:unit) : group * group = {
      var y: gf_q;
      y = $ Dgf_q.dgf_q;
      return (g^y, g^(K.x * y));
    }
  }.

  module DDHr = {
    proc orcl (x:unit) : group * group = {
      var y, z: gf_q;
      y = $ Dgf_q.dgf_q;
      z = $ Dgf_q.dgf_q;
      return (g^y, g^z);
    }
  }.

  module DDHb : H.Orclb = {
    proc leaks () : group = { 
      K.x = $ Dgf_q.dgf_q;
      return g^K.x;
    }
    proc orclL = DDHl.orcl
    proc orclR = DDHr.orcl
  }.

  lemma islossless_leaks : islossless DDHb.leaks.
  proof. proc;auto;progress;smt. qed.

  lemma islossless_orcl1 : islossless DDHb.orclL.
  proof. proc;auto;progress;smt. qed.

  lemma islossless_orcl2 : islossless DDHb.orclR.
  proof. proc;auto;progress;smt. qed.

  clone DArrayWhile2 as L with 
    type t1<-gf_q,
    type t2<-gf_q,
    type t<-group*group.

  section.

    (** A specific instance of the DDH.Game is obtained when we restrict Ln/Rn to
    a single oracle call (through the H.B(-) adversary construction) *)
    module ADDH(A:Adv_t) : DDH.Adv_t = {
      var l0: int

      proc init() : unit = {
        A.init();
        l0 = $[0..nmax-1];
      }
      
      proc solve(gx:group, gy:group, gz:group): bool = {
        var gyzs: (group*group) array;
        var y, z: gf_q;
        var b': bool;
        var i:int;
        i = 0;
        gyzs = offun (fun k, (g,g)) nmax; (* just a default value *)
        while (i<nmax) {
          if (l0 < i) {
          y = $Dgf_q.dgf_q;
          gyzs.[i] = (g^y, gx^y);
          }
          else {
            if (l0=i) {
              gyzs.[i] = (gy,gz);
            }
            else {
              y = $Dgf_q.dgf_q;
              z = $Dgf_q.dgf_q;
              gyzs.[i] = (g^y,g^z);
            }
          }
          i = i+1;
        }
        b' = A.solve(gx, gyzs);
        return b';
      }
    }.

    lemma ADDH_init_ll (A<:Adv_t):
      islossless A.init => islossless ADDH(A).init.
    proof.
      move=> H; proc; rnd; call (_:true) => //.
      skip. progress.
      rewrite DInterval.mu_dinter size_filter count_predT size_range ?max_ler; first by smt.
      by smt.
    qed.

    lemma ADDH_solve_ll (A<:Adv_t):
      islossless A.solve => islossless ADDH(A).solve.
    proof.
      move=> H; proc. 
      call (_:true) => //.
      while (i<=nmax) (nmax-i).
        move=> z.
        if.
          by wp; rnd; skip; progress; smt.
          if.
            by wp; skip; progress; smt.
            by wp; do 2!rnd; skip; progress; smt.
          by wp; skip; progress; smt.
    qed.

(* adversary attacking DDHnmax (obs: does not have access to the state of
 the modules used in the hybrid argument)
*)
declare module ADDHnmax : Adv_t {ADDH, H.Count, H.HybOrcl, K}.

axiom ADDHnmax_init_ll: islossless ADDHnmax.init.

axiom ADDHnmax_solve_ll: islossless ADDHnmax.solve.

(* the functor ToAdv allow us to view DDHnmax.Game as instaces of Ln/Rn games
 used by the generic Hybrid argument *)
local module ToAdv(Ob: H.Orclb, O:H.Orcl) = {
  proc main() : bool = {
    var gx: group;
    var gyzs: (group*group) array;
    var i: int;
    var b': bool;

    ADDHnmax.init();

    gx = Ob.leaks();
    gyzs = offun (fun k, (g,g)) nmax; (* just a default value *)
    i = 0;
    while (i < nmax) {
      gyzs.[i] = O.orcl();
      i = i+1;
      }
    b' = ADDHnmax.solve(gx, gyzs);
    return b';
  }
}.


require import DProd.
local equiv DDHn_Ln :
 Game(ADDHnmax).game ~ H.Ln(DDHb, ToAdv).main :
 b{1} /\ ={glob ADDHnmax} ==> ={res} /\ H.Count.c{2} <= nmax.
proof.
proc.
inline Game(ADDHnmax).game H.Count.init ToAdv(DDHb, H.OrclCount(H.L(DDHb))).main
 DDHb.leaks H.OrclCount(H.L(DDHb)).orcl H.L(DDHb).orcl DDHb.orclL.
wp; call (_: ={glob ADDHnmax, gx, gyzs} ==> ={res}); first by proc true.
rcondt {1} 5.
 move => &1; rnd; rnd; rnd. 
 by call (_: true); skip; trivial.
simplify.
seq 2 4: (b{1} /\ ={glob ADDHnmax} /\ H.Count.c{2} = 0 /\ x{1}=K.x{2}
          /\ gx{2} = g^K.x{2}).
 by auto; call (_: true); wp.
transitivity {1} {
  gyzs = L.M.gen2(nmax,Dgf_q.dgf_q,Dgf_q.dgf_q,(fun a b, (g^a,g^(x *a))));
 }
 ( ={glob ADDHnmax, x} /\ b{1} ==> ={glob ADDHnmax, gyzs, x} /\ b{1})
 ( ={glob ADDHnmax} /\ x{1}=K.x{2} /\ H.Count.c{2}=0 /\ gx{2}=g^K.x{2}
  ==> ={glob ADDHnmax, gyzs} /\ g^x{1}=gx{2} /\ H.Count.c{2} <= nmax).
   by progress; exists (glob ADDHnmax){2} K.x{2}; trivial.
  by progress; smt.
 by inline L.M.gen2; wp; do 2!rnd; wp; skip; progress.
cut Hnmax: 0 <= nmax by smt.
transitivity {2} {
  gyzs = L.M.gen1(nmax,Dgf_q.dgf_q,Dgf_q.dgf_q,(fun a b, (g^a,g^(K.x *a))),(g,g));
 }
 ( ={glob ADDHnmax} /\ x{1}=K.x{2} ==> ={glob ADDHnmax, gyzs} /\ x{1}=K.x{2})
 ( ={glob ADDHnmax, K.x} /\ H.Count.c{2}=0 /\ gx{2}=g^K.x{2}
  ==> ={glob ADDHnmax, gyzs} /\ g^K.x{1}=gx{2} /\ H.Count.c{2} <= nmax).
   by progress; exists (glob ADDHnmax){2} K.x{2}; trivial.
  by progress.
 symmetry.
 by call L.darray2_loop_equiv.
inline L.M.gen1. 
wp; while (={K.x} /\ len{1}=nmax /\ i0{1} = i{2} /\ H.Count.c{2}=i{2} /\ i{2} <= nmax /\ f{1}=(fun a b, (g^a,g^(K.x{1}*a)))
 /\ d1{1}=Dgf_q.dgf_q /\ d2{1}=Dgf_q.dgf_q 
 /\ size z{1} = nmax /\ size gyzs{2} = nmax
 /\ (forall k, 0 <= k < i{2} => z{1}.[k]=gyzs{2}.[k])).
 inline H.Count.incr; wp; rnd{1}; rnd.
by auto; progress; smt.
wp; skip; progress; first 2 smt.
apply arrayP; split; first by smt.
smt. 
qed.

local lemma DDHn_Ln_pr &m:
 Pr[ Game(ADDHnmax).game(true) @ &m : res]
 = Pr[H.Ln(DDHb, ToAdv).main() @ &m : res /\ H.Count.c <= nmax]
by byequiv DDHn_Ln.

local equiv DDHn_Rn:
 Game(ADDHnmax).game ~ H.Rn(DDHb, ToAdv).main :
 !b{1} /\ ={glob ADDHnmax} ==> res{1}=!res{2} /\ H.Count.c{2} <= nmax. 
proof.
proc.
inline Game(ADDHnmax).game H.Count.init ToAdv(DDHb, H.OrclCount(H.R(DDHb))).main
   DDHb.leaks H.OrclCount(H.R(DDHb)).orcl H.R(DDHb).orcl DDHb.orclR.
wp; call (_: ={glob ADDHnmax, gx, gyzs} ==> ={res}); first by proc true.
rcondf {1} 5.
 move => &1; rnd; rnd; rnd. 
 by wp; call (_: true); skip; trivial.
simplify.
seq 2 4: (!b{1} /\ ={glob ADDHnmax} /\ H.Count.c{2} = 0 /\ x{1}=K.x{2}
          /\ gx{2} = g^K.x{2}).
 by auto; call (_: true); wp.
transitivity {1} {
  gyzs = L.M.gen2(nmax,Dgf_q.dgf_q,Dgf_q.dgf_q,(fun a b, (g^a,g^b)));
 }
 ( ={glob ADDHnmax, x} /\ !b{1} ==> ={glob ADDHnmax, gyzs, x} /\ !b{1})
 ( ={glob ADDHnmax} /\ x{1}=K.x{2} /\ H.Count.c{2}=0 /\ gx{2}=g^K.x{2}
  ==> ={glob ADDHnmax, gyzs} /\ g^x{1}=gx{2} /\ H.Count.c{2} <= nmax).
   by progress; exists (glob ADDHnmax){2} K.x{2}; trivial.
  by progress; smt.
 by inline L.M.gen2; wp; do 2!rnd; wp; skip; progress.
cut Hnmax: 0 <= nmax by smt.
transitivity {2} {
  gyzs = L.M.gen1(nmax,Dgf_q.dgf_q,Dgf_q.dgf_q,(fun a b, (g^a,g^b)),(g,g));
 }
 ( ={glob ADDHnmax} /\ x{1}=K.x{2} ==> ={glob ADDHnmax, gyzs} /\ x{1}=K.x{2})
 ( ={glob ADDHnmax, K.x} /\ H.Count.c{2}=0 /\ gx{2}=g^K.x{2}
  ==> ={glob ADDHnmax, gyzs} /\ g^K.x{1}=gx{2} /\ H.Count.c{2} <= nmax).
   by progress; exists (glob ADDHnmax){2} K.x{2}; trivial.
  by progress.
 symmetry.
 by call L.darray2_loop_equiv.
inline L.M.gen1. 
wp; while (={K.x} /\ len{1}=nmax /\ i0{1} = i{2} /\ H.Count.c{2}=i{2} /\ i{2} <= nmax /\ f{1}=(fun a b, (g^a,g^b))
 /\ d1{1}=Dgf_q.dgf_q /\ d2{1}=Dgf_q.dgf_q 
 /\ size z0{1} = nmax /\ size gyzs{2} = nmax
 /\ (forall k, 0 <= k < i{2} => z0{1}.[k]=gyzs{2}.[k])).
 inline H.Count.incr; wp; rnd; rnd.
by auto; progress; smt.
wp; skip; progress; first 2 smt.
apply arrayP; split; first by smt.
smt. 
qed.

local lemma DDHn_Rn_pr &m:
 Pr[ Game(ADDHnmax).game(false) @ &m : !res]
 = Pr[H.Rn(DDHb, ToAdv).main() @ &m : res /\ H.Count.c <= nmax]
by byequiv DDHn_Rn.

local equiv DDH_L1:
 DDH.Game(ADDH(ADDHnmax)).game ~ H.Ln(DDHb, H.HybGame(ToAdv)).main :
 b{1} /\ ={glob ADDHnmax} ==> ={res} /\ H.HybOrcl.l{2} <= nmax /\ H.Count.c{2} <= 1.
proof.
proc.
inline H.HybGame(ToAdv, DDHb, H.OrclCount(H.L(DDHb))).main
 H.HybGame(ToAdv, DDHb, H.OrclCount(H.L(DDHb))).A.main
 ADDH(ADDHnmax).init ADDH(ADDHnmax).solve H.HybOrcl(DDHb, H.OrclCount(H.L(DDHb))).orcl
   DDHb.orclL DDHb.orclR H.OrclCount(H.L(DDHb)).orcl DDHb.leaks.
wp; call (_: ={glob ADDHnmax, gx, gyzs} ==> ={res}); first by proc true.
seq 3 5: (b{1} /\ ADDH.l0{1}=H.HybOrcl.l0{2} /\ x{1}=K.x{2} /\
          0 <= H.HybOrcl.l0{2} < nmax /\
          H.HybOrcl.l{2}=0 /\ H.Count.c{2} = 0 /\ ={glob ADDHnmax}).
 rnd; seq 2 4: (b{1} /\ H.Count.c{2}=0 /\ ADDH.l0{1}=H.HybOrcl.l0{2} /\
                0 <= H.HybOrcl.l0{2} < nmax /\ H.HybOrcl.l{2}=0 /\
                ={glob ADDHnmax}).
 swap {1} 2 -1.
 call (_: ={glob ADDHnmax} ==> ={glob ADDHnmax, res}); first by proc true.
  inline H.Count.init; wp; rnd; wp.
  by skip; progress; smt.
 done.
swap {1} 4 -3; sp.
splitwhile{1} 8: (i < ADDH.l0 /\ x=x /\ b=b).
splitwhile{2} 1: (i < H.HybOrcl.l0).
simplify.
transitivity {1} {
 y = $Dgf_q.dgf_q;
 z = $Dgf_q.dgf_q;
 gxy = b ? g ^ (x * y) : g ^ z;
 gy = g ^ y;
 gz = gxy;
 i = 0;
 gyzs = offun (fun k, (g,g)) nmax;
 while (i < nmax /\ i < ADDH.l0) {
  y0 = $Dgf_q.dgf_q;
  z0 = $Dgf_q.dgf_q;
  gyzs.[i] = (g ^ y0, g ^ z0);
  i = i + 1;
 }
 while (i < nmax) {
  if (ADDH.l0 < i) {
    y0 = $Dgf_q.dgf_q;
    gyzs.[i] = (g ^ y0, gx ^ y0);
  } else {
    if (ADDH.l0 = i) {
      gyzs.[i] = (gy, gz);
    } else {
      y0 = $Dgf_q.dgf_q;
      z0 = $Dgf_q.dgf_q;
      gyzs.[i] = (g ^ y0, g ^ z0);
    }
  }
  i = i + 1;
 }
}
( ={glob ADDHnmax,ADDH.l0,b,x,gx} /\ 0 <= ADDH.l0{2}
  ==> ={glob ADDHnmax,b,y,z,gx,gy,gz,i,gyzs,ADDH.l0} )
( ={glob ADDHnmax} /\ gx{2} = g ^ K.x{2} /\
  gyzs{2} = offun (fun k, (g,g)) nmax /\
  i{2} = 0 /\
  gx{1} = g ^ x{1} /\
  b{1} /\
  ADDH.l0{1} = H.HybOrcl.l0{2} /\
  0 <= H.HybOrcl.l0{2} < nmax /\
  x{1} = K.x{2} /\ H.HybOrcl.l{2} = 0 /\ H.Count.c{2}=0
  ==> ={glob ADDHnmax, gx, gyzs} /\ b{1} /\ H.Count.c{2} <= 1
      /\ H.HybOrcl.l{2}<=nmax).
   by progress; exists (glob ADDHnmax){2} H.HybOrcl.l0{2} b{1} (g^K.x{2}) K.x{2}.
  by progress; smt. 
 sim.
 while (={gyzs,i,x,y,z,gz,gy,gx,z,y,b,ADDH.l0, glob ADDHnmax} /\
        i{2} <= ADDH.l0{2}).
  rcondf {1} 1; first by move=> &m; skip; progress; smt.
  rcondf {1} 1; first by move=> &m; skip; progress; smt.
  by wp; do 2! rnd; skip; progress; smt.
 by wp; do 2! rnd; skip; progress.

swap {1} [1..5] 3.
unroll {1} 9; unroll {2} 2.

seq 3 1: (={glob ADDHnmax,i,gyzs} /\
  gx{2} = g ^ K.x{2} /\
  i{2} = H.HybOrcl.l0{2} /\
  gx{1} = g ^ x{1} /\
  b{1} /\
  ADDH.l0{1} = H.HybOrcl.l0{2} /\
  0 <= H.HybOrcl.l0{2} < nmax /\
  x{1} = K.x{2} /\ H.HybOrcl.l{2} = i{2} /\ H.Count.c{2}=0
  /\ i{2} = H.HybOrcl.l0{2}).
 sp; while ( ={glob ADDHnmax, i, gx, gyzs} /\ b{1} /\
            0 <= H.HybOrcl.l0{2} < nmax /\
            ADDH.l0{1} = H.HybOrcl.l0{2} /\ x{1}=K.x{2} /\
            gx{1}=g^x{1} /\ H.HybOrcl.l{2}=i{2} /\
            i{2}<=H.HybOrcl.l0{2} /\ H.Count.c{2}=0).
  rcondf {2} 2; first by move => &m; wp; skip; progress; smt.
  rcondf {2} 2; first by move => &m; wp; skip; progress; smt.
  auto; progress; smt.
  by wp; skip; smt.
rcondt {2} 1; first by move=> &m; skip; progress.
rcondf {2} 2; first by move=> &m; wp; skip; progress.
rcondt {2} 2; first by move=> &m; wp; skip; progress.
rcondt {1} 6; first by move=> &m; wp; do 2!rnd; skip; progress.
rcondf {1} 6; first by move=> &m; wp; do 2!rnd; skip; progress.
rcondt {1} 6; first by move=> &m; wp; do 2!rnd; skip; progress.
inline H.L(DDHb).orcl DDHb.orclL H.Count.incr.
while (={glob ADDHnmax, gx, gyzs,i} /\ b{1} /\ H.Count.c{2} <= 1
/\ gx{2}=g^K.x{2}
/\ H.HybOrcl.l0{2} < i{2}
/\ ADDH.l0{1} = H.HybOrcl.l0{2}
/\ i{2}=H.HybOrcl.l{2}
/\ i{2}<=nmax).
 rcondt {1} 1; first by move=> &m; skip; progress.  
 rcondt {2} 2; first by move=> &m; wp; skip; progress. 
 by auto; smt.
 by wp; rnd{1}; auto; smt.
qed.

local lemma DDH_L1_pr &m:
 Pr[DDH.Game(ADDH(ADDHnmax)).game(true) @ &m : res]
 = Pr[H.Ln(DDHb, H.HybGame(ToAdv)).main() @ &m : (res /\ H.HybOrcl.l <= nmax) /\ H.Count.c <= 1]
 by byequiv DDH_L1.

local equiv DDH_R1:
 DDH.Game(ADDH(ADDHnmax)).game ~ H.Rn(DDHb, H.HybGame(ToAdv)).main :
 !b{1} /\ ={glob ADDHnmax} ==> res{1}=!res{2} /\ H.HybOrcl.l{2} <= nmax /\ H.Count.c{2} <= 1.
proof.
proc.
inline H.HybGame(ToAdv, DDHb, H.OrclCount(H.R(DDHb))).main
 H.HybGame(ToAdv, DDHb, H.OrclCount(H.R(DDHb))).A.main
 ADDH(ADDHnmax).init ADDH(ADDHnmax).solve H.HybOrcl(DDHb, H.OrclCount(H.R(DDHb))).orcl
 DDHb.orclL DDHb.orclR H.OrclCount(H.R(DDHb)).orcl DDHb.leaks.
wp; call (_: ={glob ADDHnmax, gx, gyzs} ==> ={res}); first by proc true.
seq 3 5: (!b{1} /\ ADDH.l0{1}=H.HybOrcl.l0{2} /\ x{1}=K.x{2} /\
          0 <= H.HybOrcl.l0{2} < nmax /\
          H.HybOrcl.l{2}=0 /\ H.Count.c{2} = 0 /\ ={glob ADDHnmax}).
 rnd; seq 2 4: (!b{1} /\ H.Count.c{2}=0 /\ ADDH.l0{1}=H.HybOrcl.l0{2} /\
                0 <= H.HybOrcl.l0{2} < nmax /\ H.HybOrcl.l{2}=0 /\
                ={glob ADDHnmax})=> //.
 swap {1} 2 -1.
 call (_: true).
 by inline H.Count.init; auto; smt.
swap {1} 4 -3; sp.
splitwhile{1} 8: (i < ADDH.l0 /\ x=x /\ b=b).
splitwhile{2} 1: (i < H.HybOrcl.l0).
simplify.
transitivity {1} {
 y = $Dgf_q.dgf_q;
 z = $Dgf_q.dgf_q;
 gxy = b ? g ^ (x * y) : g ^ z;
 gy = g ^ y;
 gz = gxy;
 i = 0;
 gyzs = offun (fun k, (g,g)) nmax;
 while (i < nmax /\ i < ADDH.l0) {
  y0 = $Dgf_q.dgf_q;
  z0 = $Dgf_q.dgf_q;
  gyzs.[i] = (g ^ y0, g ^ z0);
  i = i + 1;
 }
 while (i < nmax) {
  if (ADDH.l0 < i) {
    y0 = $Dgf_q.dgf_q;
    gyzs.[i] = (g ^ y0, gx ^ y0);
  } else {
    if (ADDH.l0 = i) {
      gyzs.[i] = (gy, gz);
    } else {
      y0 = $Dgf_q.dgf_q;
      z0 = $Dgf_q.dgf_q;
      gyzs.[i] = (g ^ y0, g ^ z0);
    }
  }
  i = i + 1;
 }
}
( ={glob ADDHnmax,ADDH.l0,b,x,gx} /\ 0 <= ADDH.l0{2}
  ==> ={glob ADDHnmax,b,y,z,gx,gy,gz,i,gyzs,ADDH.l0} )
( ={glob ADDHnmax} /\ gx{2} = g ^ K.x{2} /\
  gyzs{2} = offun (fun k, (g,g)) nmax /\
  i{2} = 0 /\
  gx{1} = g ^ x{1} /\
  !b{1} /\
  ADDH.l0{1} = H.HybOrcl.l0{2} /\
  0 <= H.HybOrcl.l0{2} < nmax /\
  x{1} = K.x{2} /\ H.HybOrcl.l{2} = 0 /\ H.Count.c{2}=0
  ==> ={glob ADDHnmax, gx, gyzs} /\ !b{1} /\ H.Count.c{2} <= 1
      /\ H.HybOrcl.l{2}<=nmax).
   by progress; exists (glob ADDHnmax){2} H.HybOrcl.l0{2} b{1} (g^K.x{2}) K.x{2}.
  by progress; smt. 
 sim.
 while (={gyzs,i,x,y,z,gz,gy,gx,z,y,b,ADDH.l0, glob ADDHnmax} /\
        i{2} <= ADDH.l0{2}).
  rcondf {1} 1; first by move=> &m; skip; progress; smt.
  rcondf {1} 1; first by move=> &m; skip; progress; smt.
  by wp; do 2! rnd; skip; progress; smt.
 by wp; do 2! rnd; skip; progress.

swap {1} [1..5] 3.
unroll {1} 9; unroll {2} 2.

seq 3 1: (={glob ADDHnmax,i,gyzs} /\
  gx{2} = g ^ K.x{2} /\
  i{2} = H.HybOrcl.l0{2} /\
  gx{1} = g ^ x{1} /\
  !b{1} /\
  ADDH.l0{1} = H.HybOrcl.l0{2} /\
  0 <= H.HybOrcl.l0{2} < nmax /\
  x{1} = K.x{2} /\ H.HybOrcl.l{2} = i{2} /\ H.Count.c{2}=0
  /\ i{2} = H.HybOrcl.l0{2}).
 sp; while ( ={glob ADDHnmax, i, gx, gyzs} /\ !b{1} /\
            0 <= H.HybOrcl.l0{2} < nmax /\
            ADDH.l0{1} = H.HybOrcl.l0{2} /\ x{1}=K.x{2} /\
            gx{1}=g^x{1} /\ H.HybOrcl.l{2}=i{2} /\
            i{2}<=H.HybOrcl.l0{2} /\ H.Count.c{2}=0).
  rcondf {2} 2; first by move => &m; wp; skip; progress; smt.
  rcondf {2} 2; first by move => &m; wp; skip; progress; smt.
  by auto; smt.
 by skip; smt.
rcondt {2} 1; first by move=> &m; skip; progress.
rcondf {2} 2; first by move=> &m; wp; skip; progress.
rcondt {2} 2; first by move=> &m; wp; skip; progress.
rcondt {1} 6; first by move=> &m; wp; do 2!rnd; skip; progress.
rcondf {1} 6; first by move=> &m; wp; do 2!rnd; skip; progress.
rcondt {1} 6; first by move=> &m; wp; do 2!rnd; skip; progress.
inline H.R(DDHb).orcl DDHb.orclR H.Count.incr.
while (={glob ADDHnmax, gx, gyzs,i} /\ !b{1} /\ H.Count.c{2} <= 1
/\ gx{2}=g^K.x{2}
/\ H.HybOrcl.l0{2} < i{2}
/\ ADDH.l0{1} = H.HybOrcl.l0{2}
/\ i{2}=H.HybOrcl.l{2}
/\ i{2}<=nmax).
 rcondt {1} 1; first by move=> &m; skip; progress.  
 rcondt {2} 2; first by move=> &m; wp; skip; progress. 
 by auto; smt.
 by auto; smt.
qed.

local lemma DDH_R1_pr &m:
 Pr[DDH.Game(ADDH(ADDHnmax)).game(false) @ &m : !res]
 = Pr[H.Rn(DDHb, H.HybGame(ToAdv)).main() @ &m : (res /\ H.HybOrcl.l <= nmax) /\ H.Count.c <= 1]
 by byequiv DDH_R1.

(* The generic hybrid argument... *)
local lemma hyb &m:
 Pr[H.Ln(DDHb, H.HybGame(ToAdv)).main() @ &m : (res /\ H.HybOrcl.l <= nmax) /\ H.Count.c <= 1 ] -
 Pr[H.Rn(DDHb, H.HybGame(ToAdv)).main() @ &m : (res /\ H.HybOrcl.l <= nmax) /\ H.Count.c <= 1 ] = 
 1%r / nmax%r *
  (Pr[H.Ln(DDHb, ToAdv).main() @ &m : (res /\ H.Count.c <= nmax) ] -
   Pr[H.Rn(DDHb, ToAdv).main() @ &m : (res /\ H.Count.c <= nmax) ]).
proof. 
apply (H.Hybrid (<:DDHb) (<:ToAdv) _ _ _ _ &m 
       (fun (ga:glob ToAdv) (gb:glob DDHb) (c:int) (r:bool), r)).
 by apply islossless_leaks.
 by apply islossless_orcl1.
 by apply islossless_orcl2.
 move => Ob LR orcl_ll leaks_ll orcl1_ll orcl2_ll.
 proc.
 call (_:true); first by apply ADDHnmax_solve_ll.
 while true (nmax-i).
  move=> z; wp; call (_:true) => //; skip; progress; smt.
 wp; call (_:true) => //.
 call (_:true); first by apply ADDHnmax_init_ll.
 skip; progress; smt.
qed.

lemma DDHnmax_adv_bound: forall &m epsilon,
 `| 2%r * Pr[ DDH.Game(ADDH(ADDHnmax)).main() @ &m: res ] - 1%r| <= epsilon =>
 `| 2%r * Pr[ Game(ADDHnmax).main() @ &m: res ] - 1%r| <= nmax%r * epsilon.
proof.
move => &m epsilon.
move: ADDHnmax_init_ll ADDHnmax_solve_ll => H1_ll H2_ll.
rewrite (DDH.DDH_adv &m (ADDH(ADDHnmax))) //.
  by apply (ADDH_init_ll ADDHnmax).
 by apply (ADDH_solve_ll ADDHnmax).
rewrite (DDH_adv &m ADDHnmax) //.
rewrite (DDH_L1_pr &m) (DDH_R1_pr &m) (DDHn_Ln_pr &m) (DDHn_Rn_pr &m) (hyb &m).
move: (Pr[H.Ln(DDHb, ToAdv).main() @ &m : res /\ H.Count.c <= nmax] -
       Pr[H.Rn(DDHb, ToAdv).main() @ &m : res /\ H.Count.c <= nmax]) => adv.
cut Hpos: 0%r <= 1%r / nmax%r by smt.
cut H1: Real.zero <= nmax%r by smt. 
cut ->: `|(1%r / nmax%r) * adv| = 1%r / nmax%r * `|adv| by smt. 
cut H2: 0%r <= `| adv| by smt.
move=> H. smt.
qed.

end section.

end DDHnmax.

(** List variation of the Decisional Diffie-Hellman problem (dynamic size)

   Inputs: g^a and a list (array) of pairs (g^b1, g^c1), ..., (g^bn, g^cn)
   Output: a boolean b, trying to guess if ci = a * bi

*)
theory DDHn.

op nmax:int.
axiom nmax_pos: 0 < nmax.

  module type Adv_t = {
    proc choose_n(): int
    proc solve(gx:group, gyzs:(group*group) array): bool
  }.

  module Game (A:Adv_t) = {
    proc game(b:bool): bool = {
      var n: int;
      var x:gf_q;
      var y,z:gf_q array;
      var gyzs:(group*group) array;
      var guess:bool;

      n = A.choose_n();
      n = (0 <= n <= nmax) ? n : 0;

      x = $Dgf_q.dgf_q;
      y = $Darray.darray Dgf_q.dgf_q n;
      z = $Darray.darray Dgf_q.dgf_q n;

      if (b)
       gyzs = offun (fun k, (g^y.[k], g^(x*y.[k]))) n;
      else
       gyzs = offun (fun k, (g^y.[k], g^(z.[k]))) n;
 
      guess = A.solve(g^x, gyzs);

      return guess=b;
    }
    proc main(): bool = {
      var b, adv: bool;
      b = ${0,1};
      adv = game(b);
      return adv;
    }
  }.

(** Advantage definition *)
lemma DDHn_adv &m (A<:Adv_t):
  islossless A.choose_n =>
  islossless A.solve =>
  2%r * Pr[Game(A).main()  @ &m: res] - 1%r
  = Pr[Game(A).game(true)  @ &m: res] 
    - Pr[Game(A).game(false)  @ &m: !res].
proof.
  move=> Ainit_ll Asolve_ll.
  rewrite Pr [mu_not].
  pose p1:= Pr[Game(A).game(true) @ &m : res].
  pose p2:= Pr[Game(A).game(false) @ &m : res].
  (* lossless condition *)
  cut ->: Pr[Game(A).game(false) @ &m : true] = 1%r.
    byphoare (_:true)=> //.
    proc.
    by call (_:true) => //; wp; do 3!rnd; wp; call (_:true) => //; skip; smt tmo=10.
  cut Hp1: phoare [Game(A).game: b /\ (glob A)=(glob A){m} ==> res] = p1.
    bypr=> &m' [b' gA]; rewrite /p1 b'.
    by byequiv (_: ={b, glob A} ==> ={res})=> //; first by sim.
  cut Hp2: phoare [Game(A).game: !b /\ (glob A)=(glob A){m} ==> res] = p2.
    bypr=> &m' ; rewrite -neqF; move => [b' gA]; rewrite /p2 b'.
    byequiv (_: ={b, glob A} ==> ={res})=> //; first by sim.
  cut Hp: phoare [Game(A).main: (glob A)=(glob A){m} ==> res] = ((p1+p2)/2%r).
    proc.
    seq 1: b (1%r / 2%r) p1 (1%r / 2%r) p2 ((glob A)=(glob A){m}).
      by auto.
      by rnd ((=) true); skip; smt.
      by call Hp1.
      by rnd ((=) false); skip; smt.
      by call Hp2.
      smt.
  cut ->: Pr[Game(A).main() @ &m : res] = ((p1+p2)/2%r).
    by byphoare Hp.
  smt.
qed.

clone DDHnmax with op nmax <- nmax.

module ADDHnmax (A: Adv_t) : DDHnmax.Adv_t = {
  var n: int

  proc init() : unit = {
    n = A.choose_n();
    n = (0 <= n <= nmax) ? n : 0;
  }

  proc solve(gx:group, gyzs:(group*group) array) : bool = {
    var b': bool;
    var ndiff: int;
    var xx:(group*group) array;

    (* truncate the arrays!!! ---  fill the difference... *)
    xx = take n gyzs;

    b' = A.solve(gx, xx);
    return b';
  }
}.

import DProd.
clone DArrayTake with type t <- gf_q.

equiv DDHn_nmax (A <: DDHn.Adv_t {ADDHnmax}) :
 DDHn.Game(A).main ~ DDHnmax.Game(ADDHnmax(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline DDHn.Game(A).game DDHnmax(ADDHnmax(A)).Game.game
 ADDHnmax(A).init ADDHnmax(A).solve.
wp; call (_: ={glob A, gx, gyzs} ==> ={res}); first by proc true.

seq 5 5: (={x, b0, glob A} /\ 0 <= n{1} <= nmax /\ n{1}=ADDHnmax.n{2}).
 rnd; wp; call (_: ={glob A} ==> ={glob A, res}); first by proc true.
 by wp; rnd; skip; progress; smt.

transitivity {2} {
  y = $Darray.darray Dgf_q.dgf_q nmax;
  y = take ADDHnmax.n y;
  z = $Darray.darray Dgf_q.dgf_q nmax;
  z = take ADDHnmax.n z;
  gyzs = offun (fun k, (g ^ y.[k],
        if b0 then g ^ (x * y.[k]) else g^z.[k])) ADDHnmax.n;
  }
  ( ={glob A,b0,x} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1}=ADDHnmax.n{2}
    ==> ={gyzs,x,b0,glob A} )
  ( ={glob A,b0,x,ADDHnmax.n}  /\ 0 <= ADDHnmax.n{2} <= nmax 
    ==> ={x,b0,ADDHnmax.n,glob A} /\ g^x{2}=gx{2} /\ gyzs{1}=xx{2}).
   progress.
   by exists (glob A){2} ADDHnmax.n{2} b0{2} x{2}; smt.
  by progress.
 wp 2 4.
 seq 1 2: (={glob A, b0, x, y} /\
           0 <= ADDHnmax.n{2} <= nmax /\ n{1}=ADDHnmax.n{2}).
  transitivity {1} {
   y = DArrayTake.M.gen1(n,Dgf_q.dgf_q);
   }
   ( ={glob A, b0, x, n} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} ==> ={glob A, b0, x, y, n} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2})
   ( ={glob A, b0, x} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2}
      ==> ={glob A, b0, x, y} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} ).
     by progress; exists (glob A){2} ADDHnmax.n{2} b0{2} ADDHnmax.n{2}
          x{2}; smt.
    by progress.
   by inline DArrayTake.M.gen1; wp; rnd; wp; skip; progress.
  transitivity {2} {
   y = DArrayTake.M.gen2(nmax,ADDHnmax.n,Dgf_q.dgf_q);
   }
   ( ={glob A, b0, x} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2}
     ==> ={glob A, b0, x, y} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} )
   ( ={glob A, b0, x, ADDHnmax.n} ==> ={glob A, b0, x, y, ADDHnmax.n} ). 
     by progress; exists (glob A){2} ADDHnmax.n{2} b0{2} x{2}; smt.
    by progress.
   by call DArrayTake.darray_take_equiv.
  by inline DArrayTake.M.gen2; wp; rnd; wp; skip; progress; rewrite ?takeE. 
 conseq (_: ={glob A, b0, x, y} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} ==> ={glob A, b0, x, y, z} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2}); first by progress.
 transitivity {1} {
  z = DArrayTake.M.gen1(n,Dgf_q.dgf_q);
  }
  ( ={glob A, b0, x, y, n} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} ==> ={glob A, b0, x, y, z, n} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2})
  ( ={glob A, b0, x, y} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2}
     ==> ={glob A, b0, x, y, z} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} ).
    by progress; exists (glob A){2} ADDHnmax.n{2} b0{2} ADDHnmax.n{2}
         x{2}; smt.
   by progress.
  by inline DArrayTake.M.gen1; wp; rnd; wp; skip; progress.
 transitivity {2} {
  z = DArrayTake.M.gen2(nmax,ADDHnmax.n,Dgf_q.dgf_q);
  }
  ( ={glob A, b0, x, y} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2}
    ==> ={glob A, b0, x, y, z} /\ 0 <= ADDHnmax.n{2} <= nmax /\ n{1} = ADDHnmax.n{2} )
  ( ={glob A, b0, x, y, ADDHnmax.n} ==> ={glob A, b0, x, y, z, ADDHnmax.n} ). 
    by progress; exists (glob A){2} ADDHnmax.n{2} b0{2} x{2}; smt.
   by progress.
  by call DArrayTake.darray_take_equiv.
 by inline DArrayTake.M.gen2; wp; rnd; wp; skip; progress; rewrite ?takeE.

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
rewrite offunifE // get_take //=; first by smt.
rewrite get_take //=; first by smt.
rewrite offunifE //=; first by smt.
qed.

lemma DDHn_nmax_pr &m (A<:Adv_t {ADDHnmax}):
 Pr[Game(A).main() @ &m : res]
 = Pr[DDHnmax.Game(ADDHnmax(A)).main() @ &m : res] by byequiv (DDHn_nmax A).

lemma DDHn_adv_bound &m (A<:Adv_t {ADDHnmax, DDHnmax.H.Count, DDHnmax.H.HybOrcl, DDHnmax.K, DDHnmax.ADDH}) epsilon:
 islossless A.choose_n =>
 islossless A.solve =>
 `| 2%r * Pr[ DDH.Game(DDHnmax.ADDH(ADDHnmax(A))).main() @ &m: res ] - 1%r| <= epsilon =>
 `| 2%r * Pr[ Game(A).main() @ &m: res ] - 1%r| <= nmax%r * epsilon.
proof.
move=> A_choose_ll A_solve_ll; rewrite (DDHn_nmax_pr &m A).
apply (DDHnmax.DDHnmax_adv_bound (ADDHnmax(A)) _ _ &m).
  by proc; wp; call A_choose_ll.
  by proc; call A_solve_ll; wp.
qed.

end DDHn.
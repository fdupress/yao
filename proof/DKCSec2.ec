require import Array.
require import NewFMap.
require import FSet.
require import Bool.
require import Pair.
require import Option.
require import Int.
require import IntDiv.
require import Distr.
require import List.
require import Real.
require import DBool.

require import DKC.
require ExtWord.

require import ArrayExt.

theory DKCSecurity.
  clone import ExtWord as W.

  clone import DKC.DKCScheme as D with
    type tweak_t = word,
    type key1_t = word,
    type key2_t = word,
    type msg_t = word,
    type cipher_t = word.

  const bound : int.
  axiom bound_pos : 1 < bound.

  const boundl : int.
  axiom boundl_pos : 1 < boundl < bound.
  
  (* i * j * pos * tweak *)
  type query_DKC = bool * (int * bool) * (int * bool) * (int * bool) * tweak_t.

  (* Desirable to have some op/pred attesting the validity of a DKC query *)
  
  type answer_DKC = key1_t * key2_t * cipher_t.

  op bad : answer_DKC.

  module type DKC_AdvOracle = { proc encrypt(q:query_DKC): answer_DKC }.

  module type Adv_DKC_t(O:DKC_AdvOracle) = {
    proc get_challenge(lsb : bool, l:int) : bool
  }.

  module type DKC_AdvOracles = {
    proc initialize(b: bool, l: int) : bool
    proc encrypt(q : query_DKC) : answer_DKC
  }.
  
  (** DKC parameters *)
  module DKCp = {
    var b : bool
    var ksec : word
    var kpub : ((int * bool), word) fmap
    var used : tweak_t fset
    var lsb : bool
    var l : int
  }.
  
  module DKC_O : DKC_AdvOracles = {    
    
    proc initialize(b : bool,l:int): bool = {
      var i, tok1, tok2;
      
      DKCp.b = b;
      DKCp.l = l;
      DKCp.lsb = witness;
      DKCp.ksec = witness;
      DKCp.used = FSet.fset0;
      DKCp.kpub = map0;
      
      (*i = 0;
      while (i < bound) {
        DKCp.kpub.[(i, false)] = witness;
        DKCp.kpub.[(i, true)] = witness;
        i = i + 1;
      }*)
            
      i = 0;
      while (i < bound) {
        if (i = DKCp.l) {
          DKCp.lsb = ${0,1};
          DKCp.ksec = $Dword.dwordLsb DKCp.lsb;
          DKCp.kpub.[(i,DKCp.lsb)] = witness; (* can never return or encrypt this key *)
          DKCp.kpub.[(i,!DKCp.lsb)] = $Dword.dwordLsb (!DKCp.lsb);  
        }
        else {
          tok1 = $Dword.dwordLsb false;
          tok2 = $Dword.dwordLsb true;
            DKCp.kpub.[(i, false)] = tok1;
            DKCp.kpub.[(i, true)] = tok2;
        }
        i = i + 1;
      }
      
      return DKCp.lsb;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb : word;
      var xx : msg_t;
      var ib,jb,lb : int * bool;
      var bi,bj,bl', rn: bool;
      var ki, kj : word;
      var t : tweak_t;
      var ans : answer_DKC;

      ans = bad;
      (rn,ib,jb,lb,t) = q;
      
      if (!(mem DKCp.used t) /\ 0 <= ib.`1 /\ ib.`1 < jb.`1 /\ jb.`1 < lb.`1 /\ lb.`1 < bound /\ lb <> (DKCp.l,DKCp.lsb)) {
        DKCp.used = DKCp.used `|` fset1 t; (* to do: check unicity *)
        
        ki = oget DKCp.kpub.[ib];
        kj = oget DKCp.kpub.[jb];
        
        (aa,bb) = if (ib = (DKCp.l,DKCp.lsb)) 
                  then (DKCp.ksec, kj) 
                  else (if (jb = (DKCp.l,DKCp.lsb)) 
                        then (ki, DKCp.ksec) 
                        else (ki,kj));

        xx = oget DKCp.kpub.[lb];
        
        if (((((DKCp.l,DKCp.lsb) = ib) || ((DKCp.l,DKCp.lsb) = jb)) /\ !DKCp.b) || rn) {
          xx = $Dword.dword;
        }
        ans = (ki, kj, E t aa bb xx);
      }

      return ans;
    }
  }.

  module Game(O:DKC_AdvOracles, A:Adv_DKC_t) = {

    module A=A(O)
    
    proc game(b : bool, l : int) : bool = {
      var query : query_DKC;
      var answer : answer_DKC;
      var lsb : bool;
      var b' : bool;

      lsb = O.initialize(b,l);
      b' = A.get_challenge(lsb,l);
      return b' = b;
    }

    proc main(l:int) : bool = {
      var adv : bool;
      var real : bool;
      real = ${0,1};
      adv = game(real,l);
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)

  lemma encrypt_ll : islossless DKC_O.encrypt.
  proof.
    proc => //.
    seq 2 : true => //; first by auto.
    if.
    case (((DKCp.l, DKCp.lsb) = ib || (DKCp.l, DKCp.lsb) = jb) /\ !DKCp.b || rn).
      rcondt 6; first by auto.
        by auto; smt. 
      rcondf 6; first 2 by auto. 
    trivial.
  qed.

  lemma init_ll : islossless DKC_O.initialize.
  proof.
    proc => //.
    while true (bound - i).
      move => z. if. (auto; progress; first 3 by smt) => /#. (auto; progress; first 3 by smt) => /#. 
    by auto => /#. 
  qed.
  
  lemma game_ll (O<: DKC_AdvOracles) (A <: Adv_DKC_t) :
    islossless A(O).get_challenge =>
    islossless O.initialize =>  
    islossless Game(O,A).game.
  proof. by move => Agarble_ll Oinit_ll; proc; call Agarble_ll; call Oinit_ll. qed.

  lemma main_ll (O<: DKC_AdvOracles) (A <: Adv_DKC_t) :
    islossless A(O).get_challenge =>
    islossless O.initialize =>    
    islossless Game(O,A).main.
  proof.
    move => Agarble_ll Oinit_ll; proc. 
    call (_ : true); first by call Agarble_ll; call Oinit_ll.
    by auto; smt.
  qed.
  
  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)

  (***)
  
  (** Conditional probability expansion *)
  lemma DKCGame_xpn &m (O <: DKC_AdvOracles) (A <: Adv_DKC_t{O}) x:
    islossless O.initialize =>
    islossless O.encrypt =>   
    islossless A(O).get_challenge =>
    Pr[Game(O, A).main(x)  @ &m: res]
    = 1%r/2%r * (Pr[Game(O,A).game(true,x)  @ &m: res]
      + Pr[Game(O,A).game(false,x)  @ &m: res]).
  proof.
    move => Oinitialize_ll Oencrypt_ll Aget_challenge_ll.
    pose p1 := Pr[Game(O, A).game(true,x) @ &m : res].
    pose p2 := Pr[Game(O, A).game(false,x) @ &m : res].
    byphoare (_: (glob A) = (glob A){m} /\ (glob O) = (glob O){m} /\ x = l ==> _) => //.
    proc => //.
    seq 1: real (1%r/2%r) p1 (1%r/2%r) p2 ((glob A) = (glob A){m} /\ (glob O) = (glob O){m} /\ x = l); trivial.
      by auto.
      by rnd; skip; smt.
      call (_: ((glob A) = (glob A){m} /\ (glob O) = (glob O){m} /\ x = l) /\ b ==> res)=> //.
        rewrite /p1.
        bypr=> &m' [eqA] b'. 
      byequiv (_: ={glob A, glob O, b, l} /\ b{1} ==> ={res})=> //.
        by sim. 
        by rewrite b' => /#. 
      by rnd; skip; smt.
      call (_: ((glob A) = (glob A){m} /\ (glob O) = (glob O){m} /\ x = l) /\ !b ==> res)=> //.
        rewrite /p2.
        bypr=> &m' [eqA] b'.
        byequiv (_: ={glob A, glob O, b, l} /\ !b{1} ==> ={res})=> //.
        by sim.
        by rewrite -neqF; rewrite b' => /#. 
    by idtac=>/#.
  qed.

  (** Advantage definition *)
  lemma DKCGame_adv &m (O <: DKC_AdvOracles) (A <: Adv_DKC_t{O}) x:
    islossless O.initialize =>
    islossless O.encrypt =>   
    islossless A(O).get_challenge =>
    2%r * Pr[Game(O,A).main(x)  @ &m: res] - 1%r
    = Pr[Game(O,A).game(true,x)  @ &m: res] 
      - Pr[Game(O,A).game(false,x)  @ &m: !res].
  proof.
    move=> Oinitialize_ll Oencrypt_ll Aget_challenge_ll.
    rewrite Pr [mu_not].
    pose p1:= Pr[Game(O,A).game(true,x) @ &m: res].
    pose p2:= Pr[Game(O,A).game(false,x) @ &m: res].
    cut ->: Pr[Game(O,A).game(false,x) @ &m : true] = 1%r.
      byphoare (_: true) => //.
      by apply (game_ll O A).
    cut Hp1: phoare [Game(O,A).game:
                     ((glob Game(O,A)) = (glob Game(O,A)){m} /\ x = l) /\ b ==> res] = p1.
      bypr=> &m' [eqG] b'; rewrite /p1 b'.
      by (byequiv (_: ={glob Game(O,A), l, b} ==> ={res}); first by sim; sim) => /#. 
    cut Hp2: phoare [Game(O,A).game:
                     ((glob Game(O,A)) = (glob Game(O,A)){m} /\ x = l) /\ !b ==> res] = p2.
      bypr=> &m' [eqG]; rewrite -neqF=> b'; rewrite /p2 b'.
      by (byequiv (_: ={glob Game(O,A), l, b} ==> ={res}); first by sim; sim) => /#.
    cut Hp: phoare [Game(O,A).main:
                    (glob Game(O,A)) = (glob Game(O,A)){m} /\ x = l ==> res] = ((p1+p2)/2%r).
      proc => //.
      seq 1: real (1%r / 2%r) p1 (1%r / 2%r) p2 ((glob Game(O,A)) = (glob Game(O,A)){m} /\ x = l).
        by auto.
        by rnd ((=) true); skip; smt.
        by call Hp1.
        by rnd ((=) false); skip; smt.
        by call Hp2.
        by idtac=>/#.
    cut ->: Pr[Game(O,A).main(x) @ &m : res] = ((p1+p2)/2%r).
      by byphoare Hp.
    by idtac=>/#.
  qed.
  
end DKCSecurity.
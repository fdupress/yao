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
  clone import DKCScheme.

  const bound : int.
  axiom bound_pos : 1 < bound.

  const boundl : int.
  axiom boundl_pos : 1 < boundl < bound.
  
  (* i * j * pos * tweak *)
  type query_DKC = bool * (int * bool) * (int * bool) * (int * bool) * tweak_t.

  (* Desirable to have some op/pred attesting the validity of a DKC query *)
  
  type answer_DKC = keys_t * keys_t * cipher_t.

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
    var ksec : keys_t
    var kpub : ((int * bool), keys_t) fmap
    var used : tweak_t fset
    var lsb : bool
    var l : int
  }.

  op keys_t_d : bool -> keys_t distr.
  axiom keys_t_d_ll b : is_lossless (keys_t_d b).

  op msg_t_d : msg_t distr.
  axiom msg_t_d_ll : is_lossless msg_t_d.
  
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
          DKCp.ksec = $keys_t_d DKCp.lsb;
          DKCp.kpub.[(i,DKCp.lsb)] = witness; (* can never return or encrypt this key *)
          DKCp.kpub.[(i,!DKCp.lsb)] = $keys_t_d (!DKCp.lsb);  
        }
        else {
          tok1 = $keys_t_d false;
          tok2 = $keys_t_d true;
            DKCp.kpub.[(i, false)] = tok1;
            DKCp.kpub.[(i, true)] = tok2;
        }
        i = i + 1;
      }
      
      return DKCp.lsb;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb : keys_t;
      var xx : msg_t;
      var ib,jb,lb : int * bool;
      var bi,bj,bl', rn: bool;
      var ki, kj : keys_t;
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
          xx = $msg_t_d;
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
      var b : bool;
      b = ${0,1};
      adv = game(b,l);
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
        by auto; rewrite msg_t_d_ll. 
      rcondf 6; first 2 by auto. 
    trivial.
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

end DKCSecurity.
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
  clone import ExtWord as WD.

  clone export DKC as D with
    type tweak_t = word,
    type key1_t = word,
    type key2_t = word,
    type msg_t = word,
    type cipher_t = word.

  const bound : int.
  axiom bound_pos : 1 < bound. 

  const boundl : int.
  axiom boundl_pos : 1 < boundl.

  op l : int.
  axiom l_pos : 0 <= l < boundl.
  
  (* i * j * pos * tweak *)
  type query_DKC = (int * bool) * (int * bool) * (int * bool) * word.
  type answer_DKC = word * word * word.

  op bad : answer_DKC.

  module type Adv_DKC_t = {
    proc get_challenge() : bool
  }.

  module DKCp = {
    var b : bool
    var ksec : word
    var rr : ((int * bool), word) fmap
    var kpub : ((int * bool), word) fmap
    var used : word fset
    var lsb : bool
  }.

  module type DKC_t = {
    proc initialize() : unit
    proc get_lsb() : bool
    proc encrypt(q : query_DKC) : answer_DKC
    proc get_challenge() : bool
  }.

  op itb (x:int) = if x = 1 then true else false.
  
  module DKC : DKC_t = {    

    proc get_lsb () : bool = {
      DKCp.lsb = ${0,1};
      DKCp.ksec = $Dword.dwordLsb (DKCp.lsb);

      return DKCp.lsb;
    }
    
    proc initialize(): unit = {
      var i;
            
      DKCp.used = FSet.fset0;

      DKCp.kpub = map0;
      DKCp.rr = map0;
      
      i = 0;
      while (i < bound) {
        DKCp.kpub.[(i, false)] = $Dword.dwordLsb (false);
        DKCp.kpub.[(i, true)] = $Dword.dwordLsb (true);
        i = i + 1;
      }
    }

    proc get_challenge() : bool = {
      return DKCp.b;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb,xx : word;
      var ib,jb,lb : int * bool;
      var i,j,l' : int;
      var bi,bj,bl' : bool;
      var t, ki, kj, rj : word;
      var ans : answer_DKC;
      var b : bool;
      
      ans = bad;
      (ib,jb,lb,t) = q;
      (i,bi) = ib;
      (j,bj) = jb;
      (l',bl') = lb;
      
      if (!(mem DKCp.used t || j < i || l' < i || l' < j || (l' = l /\ bl' = DKCp.lsb))) {
        DKCp.used = DKCp.used `|` fset1 t;
        
        ki = oget DKCp.kpub.[(i, bi)];
        kj = oget DKCp.kpub.[(j, bj)];
        rj = oget DKCp.rr.[(j, bj)];

        (aa,bb) = if (i = l) then (DKCp.ksec, ki) else (if (j = l) then (ki, DKCp.ksec) else (ki,kj));
        xx = if DKCp.b then oget DKCp.kpub.[(l',bl')] else oget DKCp.rr.[(l',bl')];
        
        ans = (ki, kj, E t aa bb xx);
      }

      return ans;
    }
  }.
  
  module Game(D:DKC_t, A:Adv_DKC_t) = {

    proc game(b : bool) : bool = {
      var query : query_DKC;
      var answer : answer_DKC;
      var lsb : bool;
      var b' : bool;

      D.initialize();
      b' = A.get_challenge();
      return b' = b;
    }

    proc main() : bool = {
      var adv : bool;
      DKCp.b = ${0,1}; 
      adv = game(DKCp.b);
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)

  lemma get_challenge_ll : islossless DKC.get_challenge.
  proof. by proc. qed.

  lemma encrypt_ll : islossless DKC.encrypt.
  proof.
    proc => //.
    seq 5 : true => //; first by auto.
    if; last by trivial.
      by wp. 
  qed.

  lemma init_ll : islossless DKC.initialize.
  proof.
    proc => //.
    while (0 <= i <= bound) (bound - i).
      (auto; progress; first 3 by smt); last 2 by idtac=>/#.
    auto; progress; first 2 by smt.
  qed.

  lemma game_ll (A <: Adv_DKC_t) :
    islossless A.get_challenge =>
    islossless Game(DKC,A).game.
  proof. by move => Agarble_ll; proc; call Agarble_ll; call init_ll. qed.

  lemma main_ll (D <: DKC_t) (A <: Adv_DKC_t) :
    islossless A.get_challenge =>
    islossless Game(DKC,A).main.
  proof.
    move => Agarble_ll; proc.
    call (_ : true); first by call Agarble_ll; call init_ll.
    by auto; smt.
  qed.
  
  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)

end DKCSecurity.
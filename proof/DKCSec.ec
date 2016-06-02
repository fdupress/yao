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
    
  (* i * j * pos * tweak *)
  type query_DKC = int * int * bool * word.
  type answer_DKC = word * word * word.

  op bad : answer_DKC.

  module type Adv_DKC_t = {
    proc garble(lsb:bool) : bool
  }.

  module DKCp = {
    var b : bool
    var ksec : word
    var rr : (int, word) fmap
    var kpub : (int, word) fmap
    var used : word fset
    var lsb : bool
  }.

  module type DKC_t = {
    proc initialize() : bool
    proc encrypt(q : query_DKC) : answer_DKC
    proc get_challenge() : bool
  }.

  op itb (x:int) = if x = 1 then true else false.
  
  module DKC : DKC_t = {    
    
    proc initialize(): bool = {

      DKCp.lsb = ${0,1};
      DKCp.ksec = $Dword.dwordLsb DKCp.lsb;
      DKCp.kpub = map0;
      DKCp.used = FSet.fset0;
      DKCp.rr = map0;
      
      return DKCp.lsb;
    }

    proc get_challenge() : bool = {
      return DKCp.b;
    }

    proc get_k(i:int): word = {
      var k:word;

      k = $Dword.dwordLsb (itb (i %% 2));
      (*if (!mem (dom DKCp.kpub) i) DKCp.kpub.[i] = k;
        return oget DKCp.kpub.[i];*)
      return k;
    }

    proc get_r(i:int): word = {
      var r:word;

      r = $Dword.dword;
      (*if (!mem (dom DKCp.rr) i) DKCp.rr.[i] = r;
        return oget DKCp.rr.[i];*)

      return r;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb,xx : word;
      var i,j : int;
      var pos : bool;
      var t, ki, kj, rj : word;
      var ans : answer_DKC;
      var b : bool;
      
      ans = bad;
      (i,j,pos,t) = q;
      
      (*if (!(mem DKCp.used t || j < i)) {*)
      DKCp.used = DKCp.used `|` fset1 t;

      ki = get_k(i);
      kj = get_k(j);
      rj = get_r(j);
        
      (aa,bb) = if pos then (DKCp.ksec, ki) else (ki, DKCp.ksec);
      xx = if DKCp.b then kj else rj;
        
      ans = (ki, kj, E t aa bb xx);
      (*}*)

      return ans;
    }
  }.
  
  module Game(D:DKC_t, A:Adv_DKC_t) = {

    proc game(b : bool) : bool = {
      var query : query_DKC;
      var answer : answer_DKC;
      var lsb : bool;
      var b' : bool;

      lsb = D.initialize();
      b' = A.garble(lsb);
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

  lemma get_k_ll : islossless DKC.get_k.
  proof. by proc; auto; smt. qed.

  lemma get_r_ll : islossless DKC.get_r.
  proof. by proc; auto; smt. qed.
      
  lemma encrypt_ll : islossless DKC.encrypt.
  proof.
    proc => //.
    seq 2 : true => //; first by auto.
    by wp; call get_r_ll; call get_k_ll; call get_k_ll; wp.
  qed.

  lemma init_ll : islossless DKC.initialize.
  proof. by proc => //; auto; smt. qed.

  lemma game_ll (A <: Adv_DKC_t) :
    islossless A.garble =>
    islossless Game(DKC,A).game.
  proof. by move => Agarble_ll; proc; call Agarble_ll; call init_ll. qed.

  lemma main_ll (D <: DKC_t) (A <: Adv_DKC_t) :
    islossless A.garble =>
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
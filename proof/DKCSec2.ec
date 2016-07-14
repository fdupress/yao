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
    proc get_challenge(lsb : bool) : bool
  }.

  module DKCp = {
    var b : bool
    var ksec : word
    var kpub : ((int * bool), word) fmap
    var used : word fset
    var lsb : bool
  }.

  module type DKC_t = {
    proc initialize(b: bool) : bool
    proc encrypt(q : query_DKC) : answer_DKC
  }.

  op itb (x:int) = if x = 1 then true else false.
  
  module DKC : DKC_t = {    
    
    proc initialize(b : bool): bool = {
      var i;

      DKCp.b = b;

      DKCp.used = FSet.fset0;

      DKCp.kpub = map0;
      
      i = 0;
      while (i < bound) {
        if (i = l) {
          DKCp.lsb = ${0,1};
          DKCp.ksec = $Dword.dwordLsb (DKCp.lsb);
          DKCp.kpub.[(i,DKCp.lsb)] = witness; (* can never return or encrypt this key *)
          DKCp.kpub.[(i,!DKCp.lsb)] =  $Dword.dwordLsb (!DKCp.lsb);;
        }
        else {
            DKCp.kpub.[(i, false)] = $Dword.dwordLsb (false);
            DKCp.kpub.[(i, true)] = $Dword.dwordLsb (true);
        }
        i = i + 1;
      }
     
      return DKCp.lsb;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb,xx : word;
      var ib,jb,lb : int * bool;
      var bi,bj,bl' : bool;
      var t, ki, kj,r : word;
      var ans : answer_DKC;

      ans = bad;
      (ib,jb,lb,t) = q;
      
      if (ib.`1 < jb.`1 && ib.`1 < lb.`1 && jb.`1 < lb.`1 && lb <> (l,DKCp.lsb)) {
        DKCp.used = DKCp.used `|` fset1 t; (* verificar unicidade *)
        
        ki = oget DKCp.kpub.[ib];
        kj = oget DKCp.kpub.[jb];
        
        (aa,bb) = if (ib = lb) 
                  then (DKCp.ksec, kj) 
                  else (if (jb = lb) 
                        then (ki, DKCp.ksec) 
                        else (ki,kj));

        xx = oget DKCp.kpub.[lb];
        if ((lb = ib) || (lb = jb)) {
          r = $Dword.dword; 
          xx = if DKCp.b = false then xx else r;
        }
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

      lsb = D.initialize(b);
      b' = A.get_challenge(lsb);
      return b' = b;
    }

    proc main() : bool = {
      var adv : bool;
      var b : bool;
      b = ${0,1}; 
      adv = game(b);
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)

  lemma encrypt_ll : islossless DKC.encrypt.
  proof.
    proc => //.
    seq 2 : true => //; first by auto.
    inline*.
    if.
    seq 5 : true => //; first by auto.
    if.
    auto; by smt.
    auto.
    auto.
  qed.

  lemma init_ll : islossless DKC.initialize.
  proof.
    proc => //.
    while (0 <= i <= bound) (bound - i).
      (auto; progress; first 3 by smt); last 2 by idtac=>/#.
    auto; progress; first 4 by smt.
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
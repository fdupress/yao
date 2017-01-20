require import Int.
require import Bool.
require import Real.
require import NewFMap.
require import FSet.
require import Distr.
require import Option.
require ConcretePRF.
require IdealPRF.

require (*--*) DKC.
require (*--*) DKCSec2.
require (*--*) ExtWord.


require import ArrayExt.
require import GarbleTools.

theory SomeDKC.
  clone import ExtWord as W.
  clone ExtWord as KW with op length = W.length - 1.
  
  clone import ConcretePRF with
	type K = KW.word,
	type D = word,
	type R = word.

  clone import IdealPRF with
	type K = KW.word,
	type D = word,
	type R = word.
        
  op E(t,k1,k2,m) = (F k1 t) ^ (F k2 t) ^ m.
  op D(t,k1,k2,c) = (F k1 t) ^ (F k2 t) ^ c.

  clone import DKC.DKC as PrfDKC with
        type tweak_t = word,
        type msg_t = word,
        type key1_t = KW.word,
        type key2_t = KW.word,
        type cipher_t = word,
        op E = E,
        op D = D.

  (*prover ["Z3"].*)
        
  (** DKC security definitions, instantiated with the words defined in W *)
  clone import DKCSec2.DKCSecurity with
        theory D <- PrfDKC.

  lemma PrfDKC_correct : PrfDKC.Correct().
  proof.
    by rewrite /Correct /E /D => t k1 k2 x;
      rewrite xorwA xorwC xorwK xorw0.
  qed.
  
  (*  Prove that for all l, there exists a PRF attacker that breaks
      PRF if someone breaks DKC above; code is very simple: we simulate
      everything except the l,ksec encryption, which we simulate using
      the PRF oracle. If its the real oracle, then we are in the DKC
      game; otherwise, we are in a OTP world, because tweaks do not
      repeat. *)  

section SomeDKC_Proof.
  
declare module A : Adv_DKC_t.

op bound: int.
    
  module Param = {
    var kpub : ((int * bool), word) fmap
    var used : word fset
    var ksec : word
    var lsb : bool
    var l : int
    var tbl : (word,word) fmap
    var b : bool
  }.
  
  module O : PRF_Oracle = {
    proc f(x: D): R = {
      var ret : R;

      if (Param.b) {
        ret = PRFr_Wrapped.f(x);
      }

      else {
        if (!(mem (dom Param.tbl) x)) {
          ret = $Dword.dword;
          Param.tbl.[x] = ret;
        }
        else {
          ret = oget Param.tbl.[x];
        }
      }
      
      return ret;
    }
  }.
  
  module D(F:PRF_Oracle) : PRF_Distinguisher = {
    proc initialize(b : bool): unit = {
      var i, tok1, tok2;
      
      Param.used = FSet.fset0;
      Param.kpub = map0;
      Param.l = A.get_l();
      Param.lsb = false;
      Param.ksec = WD.zeros;
      Param.tbl = map0;
      Param.b = b;
      
      i = 0;
      while (i < bound) {
        Param.kpub.[(i, false)] = WD.zeros;
        Param.kpub.[(i, true)] = WD.zeros;
        i = i + 1;
      }
            
      i = 0;
      while (i < bound) {
        if (i = Param.l) {
          Param.lsb = ${0,1};
          Param.ksec = $Dword.dwordLsb (DKCp.lsb);
          Param.kpub.[(i,DKCp.lsb)] = witness; (* can never return or encrypt this key *)
          Param.kpub.[(i,!DKCp.lsb)] = $Dword.dwordLsb (!DKCp.lsb);  
        }
        else {
          tok1 = $Dword.dwordLsb (false);
          tok2 = $Dword.dwordLsb (true);
            Param.kpub.[(i, false)] = tok1;
            Param.kpub.[(i, true)] = tok2;
        }
        i = i + 1;
      }
    }
    
    proc work (b : bool) : bool = {
      
    }
    
    proc distinguish() : bool = {
      var adv, b: bool;

      b = ${0,1};
      
      adv = work(b);
      return (adv = b);
    }
  }.

equiv true_key l b:
0 <= l < bound =>
    [DKCSecurity.Game(DKC, A).game(b,l) ~
    IND(PRFr_Wrapped,D).main : 0 <= l{1} && b{1} = true
                               ==> ={res}].
    proof.
      proc. inline DKC.initialize PRFr_Wrapped.init D(PRFr_Wrapped).distinguish.


    
lemma PrfDKC_secure : forall &m i, 0 <= i =>
    Pr[DKCSecurity.Game(DKC, A).game(true,i)@ &m:res] - 
    Pr[DKCSecurity.Game(DKC, A).game(false,i)@ &m:!res] =
    Pr[IND(PRFr_Wrapped,D).main()@ &m:res] - Pr[IND(RandomFunction,D).main()@ &m:!res].
    move => &m i  H.
    admit.
  qed.

  end section SomeDKC_Proof.
  
end SomeDKC.
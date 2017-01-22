require import Int.
require import Bool.
require import Real.
require import NewFMap.
require import FSet.
require import Distr.
require import Option.
require import Array.

require (*--*) SomePRF.
require (*--*) DKC.
require (*--*) DKCSec2.
require (*--*) ExtWord.

require import ArrayExt.
require import GarbleTools.

theory SomeDKC.
  clone import ExtWord as W.
  clone ExtWord as KW with op length = W.length - 1.
  
  clone import SomePRF.PRF with
	type D = word,
	type R = word,
	type K = KW.word.

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

  prover ["Z3"].
        
  (** DKC security definitions, instantiated with the words defined in W *)
  clone import DKCSec2.DKCSecurity with
        theory WD <- W,
        theory D <- PrfDKC.

  lemma PrfDKC_correct : PrfDKC.Correct().
  proof.
    rewrite /Correct /E /D; by smt.
  qed.
  
  (*  Prove that for all l, there exists a PRF attacker that breaks
      PRF if someone breaks DKC above; code is very simple: we simulate
      everything except the l,ksec encryption, which we simulate using
      the PRF oracle. If its the real oracle, then we are in the DKC
      game; otherwise, we are in a OTP world, because tweaks do not
      repeat. *)
   
  op bound: int.
    
  module Param = {
    var kpub : ((int * bool), (KW.word * bool)) fmap
    var used : word fset
    var lsb : bool
    var l : int
    var tbl : (word,word) fmap
  }.

  op kw2w(kw,lsb) = if kw = witness
                    then witness
                    else let lsbi = if lsb then 1 else 0
                      in let kwi = (KW.to_int kw) * 2 + lsbi
                      in W.from_int kwi.

    op w2kw(w) = if w = witness
                    then witness
                    else let kwi = (W.to_int w) (* / 2 how to divide?*)
                          in let lsbi = W.getlsb w
                          in (KW.from_int kwi,lsbi).
    
  module DKC_Oracle(O:PRF_Oracle) = {
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb : KW.word;
      var xx : word;
      var ib,jb,lb : int * bool;
      var bi,bj,bl', rn: bool;
      var t : word;
      var ki, kj : KW.word;
      var lsbi,lsbj:bool;
      var ans : answer_DKC;
      var mask : word;

      ans = bad;
      (rn,ib,jb,lb,t) = q;
      
Param.lsb);  
        }
        else {
          tok1 = $Dword.dwordLsb (false);
          tok2 = $Dword.dwordLsb (true);
            Param.kpub.[(i, false)] = w2kw tok1;
            Param.kpub.[(i, true)] = w2kw tok2;
        }
        i = i + 1;
      }
      return Param.lsb;
    }
    
    proc distinguish(l : int) : bool = {
      var adv,lsb;

      lsb = initialize(l);
      adv = A.get_challenge(lsb,l);
      
      return adv;
    }
  }.

equiv true_key l b (A <:  Adv_DKC_t):
    DKCSecurity.Game(DKC,A).game ~
    IND(PRFr_Wrapped,D(A)).main : 0 <= l{1} < bound && b{1} = true
                               ==> ={res}.
    proof.
      proc. inline DKC.initialize PRFr_Wrapped.init D(A,PRFr_Wrapped).distinguish.
      admit.
    qed.
    
lemma PrfDKC_secure : forall (A <: Adv_DKC_t) &m i, 0 <= i < bound =>
    Pr[DKCSecurity.Game(DKC,A).game(true,i)@ &m:res] - 
    Pr[DKCSecurity.Game(DKC,A).game(false,i)@ &m:!res] =
    Pr[IND(PRFr_Wrapped,D(A)).main(i)@ &m:res] - Pr[IND(RandomFunction,D(A)).main(i)@ &m:!res].
    admit.
  qed.

  op e_prf : real.

  axiom e_prob : 0%r <= e_prf <= 1%r.

  axiom e_max_adv  : forall i &m (D <: PRF_Distinguisher),
  Pr[IND(PRFr_Wrapped,D).main(i)@ &m:res] -
  Pr[IND(RandomFunction,D).main(i)@ &m:!res] <= e_prf.
  
end SomeDKC.
require import Int.
require import IntDiv.
require import Bool.
require import Real.
require import NewFMap.
require import FSet.
require import Distr.
require import Option.
require import Array.
require import Pair.

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

  (*prover ["Z3"].*)
        
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
   
  (*op bound: int.*)
    
  module Param = {
    var kpub : ((int * bool), (KW.word * bool)) fmap
    var used : word fset
    var lsb : bool
    var l : int
    var tbl : (word,word) fmap
  }.

  op kw2w(kw,lsb) =
  (*if kw = witness then witness else*)
                   let lsbi = if lsb then 1 else 0
                      in let kwi = (KW.to_int kw) * 2 + lsbi
                      in W.setlsb (W.from_int kwi) lsb.

  op w2kw(w) =
  (*if w = witness then witness else*)
  let kwi = (W.to_int w) %/ 2 (* / 2 *)
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
  
      if (!(mem Param.used t) && ib.`1 < jb.`1 && jb.`1 < lb.`1 && lb <> (Param.l,Param.lsb)) {
        Param.used = Param.used `|` fset1 t; 
        
        (ki,lsbi) = oget Param.kpub.[ib];
        (kj,lsbj) = oget Param.kpub.[jb];
        
        (aa,bb) = if (ib = (Param.l,Param.lsb)) 
                  then (witness, kj) 
                  else (if (jb = (Param.l,Param.lsb)) 
                        then (ki, witness) 
                        else (ki,kj));

        xx = let (kxx,lsbxx) = oget Param.kpub.[lb] in kw2w kxx lsbxx;

        if (rn) {
          xx = $Dword.dword;
        }
        
        if ((Param.l,Param.lsb)=ib) {
          mask = O.f(t);
          ans = (kw2w ki lsbi, kw2w kj lsbj, mask ^ (F kj t) ^ xx);
        }
        else  {
            if ((Param.l,Param.lsb)=jb) {
              mask = O.f(t);
              ans = (kw2w ki lsbi, kw2w kj lsbj, (F ki t) ^ mask ^ xx);
           }
           else  {
              ans = (kw2w ki lsbi, kw2w kj lsbj, (F ki t) ^ (F kj t) ^ xx);
           }
        }
      }

      return ans;
    }
  }.
      
  module D(A : Adv_DKC_t,F:PRF_Oracle)  = {

    module A = A(DKC_Oracle(F))
    
    proc initialize(l:int): bool = {
      var i, tok1, tok2;
      var ki : KW.word;
      
      Param.used = FSet.fset0;
      Param.kpub = map0;
      Param.lsb = witness;
      Param.tbl = map0;
      Param.l = l;
      
      i = 0;
      while (i < bound) {
        Param.kpub.[(i, false)] = (KW.zeros,false);
        Param.kpub.[(i, true)] = (KW.zeros,true);
        i = i + 1;
      }

      i = 0;
      while (i < bound) {
        if (i = Param.l) {
          Param.lsb = ${0,1};
          Param.kpub.[(i,Param.lsb)] = witness; (* can never return or encrypt this key *)
          ki = $KW.Dword.dword;
          Param.kpub.[(i,!Param.lsb)] = (ki,(!Param.lsb));  
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
      
  
equiv true_key lp b (A <:  Adv_DKC_t):
    DKCSecurity.Game(DKC,A).game ~
    IND(PRFr_Wrapped,D(A)).main : 0 <= lp < boundl /\ b = true /\ l{1} = lp /\ l{2} = lp
                               ==> ={res}.
    proof.
      proc.
      inline PRFr_Wrapped.init D(A,PRFr_Wrapped).distinguish. 
      seq 1 3 : (0 <= lp < boundl /\ b = true /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ 
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\
      (forall k, 0 <= k < bound => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,true)] = kw2w (fst (oget Param.kpub{2}.[(k,true)])) true) /\
      (forall k, 0 <= k < bound => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,false)] = kw2w (fst (oget Param.kpub{2}.[(k,false)])) false) /\
      (forall k, 0 <= k < bound => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2})));   
      inline DKC.initialize D(A, PRFr_Wrapped).initialize.
    
        wp; while (0 <= lp < boundl /\ b = true /\ ={i} /\ 0 <= i{1} <= bound /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\
      (forall k, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,true)] = kw2w (fst (oget Param.kpub{2}.[(k,true)])) true) /\
      (forall k, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,false)] = kw2w (fst (oget Param.kpub{2}.[(k,false)])) false) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))).
        
        if; first by progress. print w2kw.
        wp. rnd (fun w, fst (w2kw w)) (fun w, kw2w w (!Param.lsb{2})). wp. rnd{1}. rnd. skip; progress.
        by rewrite Dword.dwordLsb_lossless.
        simplify w2kw kw2w fst; smt tmo=15.
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w kiR (!lsbL)) = !lsbL <=> true. simplify kw2w. rewrite get_setlsb. done. done.
        by smt.
        simplify w2kw kw2w fst; smt tmo=15. 
        idtac=>/#.
        idtac=>/#. 
        rewrite !getP => /#. 
        rewrite !getP => /#. 
        rewrite !getP => /#. 

      auto; progress; first 2 by idtac=>/#.
        rewrite !getP. case ((k, true) = (i{2}, true)) => hc. simplify kw2w w2kw. rewrite oget_some. smt tmo=30. idtac=>/#. 
        rewrite !getP. case ((k, false) = (i{2}, false)) => hc. simplify kw2w w2kw. rewrite oget_some. smt tmo=30. idtac=>/#. 
        rewrite !getP => /#. 

    wp; while (0 <= lp < boundl /\ b = true /\ ={i} /\ 0 <= i{1} <= bound /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ 
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\
      (forall k, 0 <= k < i{1} => oget DKCp.kpub{1}.[(k,false)] = W.zeros) /\
      (forall k, 0 <= k < i{1} => oget DKCp.kpub{1}.[(k,true)] = W.zeros) /\
      (forall k, 0 <= k < i{1} => oget Param.kpub{2}.[(k,false)] = (KW.zeros, false)) /\
      (forall k, 0 <= k < i{1} => oget Param.kpub{2}.[(k,true)] = (KW.zeros, true))).
      auto; progress; expect 6 by by rewrite ?getP => /#. 

    auto; progress; last 8 by idtac=>/#.
        by rewrite dK_ll. 
        by smt. 
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.

    wp. 



    
  qed.

equiv false_key l b (A <:  Adv_DKC_t):
    DKCSecurity.Game(DKC,A).game ~
    IND(RandomFunction,D(A)).main : 0 <= l{1} < bound && b{1} = false
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

  
end SomeDKC.
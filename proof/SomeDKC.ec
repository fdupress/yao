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
  clone import ExtWord as WSD.
  clone ExtWord as KW with op length = WSD.length - 1.
  
  (*************************************)
  (** AUXLIAR FUNCTIONS *)
  (*************************************)

  const bound : int.
  axiom bound_pos : 1 < bound.

  const boundl : int.
  axiom boundl_pos : 1 < boundl < bound.
  
  op kw2w(kw,lsb) =
  if kw = witness then witness else
                   let lsbi = if lsb then 1 else 0
                      in let kwi = (KW.to_int kw) * 2 + lsbi
                      in WSD.setlsb (WSD.from_int kwi) lsb.

  op kw2w'(kw,lsb) =
                   let lsbi = if lsb then 1 else 0
                      in let kwi = (KW.to_int kw) * 2 + lsbi
                      in WSD.setlsb (WSD.from_int kwi) lsb.
  
  op w2kw(w) =
  if w = witness then (witness,WSD.getlsb w) else
  let kwi = (WSD.to_int w) %/ 2 (* / 2 *)
                          in let lsbi = WSD.getlsb w
                          in (KW.from_int kwi,lsbi).

  op w2kw'(w) =
  let kwi = (WSD.to_int w) %/ 2 (* / 2 *)
                          in let lsbi = WSD.getlsb w
    in (KW.from_int kwi,lsbi).

  op kw2w(kw,lsb) =
  if kw = witness then witness else
  let lsbi = if lsb then 1 else 0
  in let kwi = (KW.to_int kw) * 2 + lsbi
    in WSD.setlsb (WSD.from_int kwi) lsb.

  
  
  lemma w2kw_kw2w w b : fst (w2kw (kw2w w b)) = w. 
  proof.
    simplify kw2w w2kw fst.
    case b => hc.
    smt tmo=60.
    simplify.
    smt tmo=60.
  qed.

  lemma kw2w_w2kw w b :
    getlsb w = b => kw2w (fst (w2kw w)) b = w.
  proof.
    move => hlsb.
    simplify kw2w w2kw fst.
    case b => hc.
    smt tmo=60.
    simplify.
    smt tmo=60.
  qed.

  lemma kw2w_w2kw' w b :
    getlsb w = b => kw2w (fst (w2kw' w)) b = w.
  proof.
    move => hlsb.
    simplify kw2w w2kw' fst.
    case b => hc.
    smt tmo=60.
    simplify.
    smt tmo=60.
  qed.
  
  lemma w2kw'_kw2w' w b : fst (w2kw' (kw2w' w b)) = w. 
  proof.
    simplify w2kw kw2w fst.
    case b => hc.
    smt tmo=60.
    simplify.
    smt tmo=60.
  qed.

  lemma kw2w'_w2kw' w b :
    getlsb w = b => kw2w' (fst (w2kw' w)) b = w.
  proof.
    move => hlsb.
    simplify kw2w w2kw fst.
    case b => hc.
    smt tmo=60.
    simplify.
    smt tmo=60.
  qed.
  
  clone import SomePRF.PRF with
	type D = word,
	type R = word,
	type K = KW.word,
        op dK = KW.Dword.dword,
        op dR = WSD.Dword.dword.
          
  clone import DKC.DKCScheme as PrfDKC with
    type tweak_t = word,
    type key1_t = word,
    type key2_t = word,
    type msg_t = word,
    type cipher_t = word,
        op E(t,k1,k2,m) = (F (fst (w2kw k1)) t) ^ (F (fst (w2kw k2)) t) ^ m,
        op D(t,k1,k2,c) = (F (fst (w2kw k1)) t) ^ (F (fst (w2kw k2)) t) ^ c.
        
  (** DKC security definitions, instantiated with the words defined in W *)
  clone import DKCSec2.DKCSecurity with
    theory W <- WSD,
    theory D <- PrfDKC,
    op bound = bound,
    op boundl = boundl.
    
  lemma PrfDKC_correct : PrfDKC.Correct().
  proof.
    by simplify Correct E D => t k1 k2 x; smt.
  qed.
  
  (*  Prove that for all l, there exists a PRF attacker that breaks
      PRF if someone breaks DKC above; code is very simple: we simulate
      everything except the l,ksec encryption, which we simulate using
      the PRF oracle. If its the real oracle, then we are in the DKC
      game; otherwise, we are in a OTP world, because tweaks do not
      repeat. *)

  (*************************************)
  (** PRF PART *)
  (*************************************)
  
  module Param = {
    var kpub : ((int * bool), (KW.word * bool)) fmap
    var used : word fset
    var lsb : bool
    var l : int
    var tbl : (word,word) fmap
  }.
    
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
  
      if (!(mem Param.used t) /\ 0 <= ib.`1 /\ ib.`1 < jb.`1 /\ jb.`1 < lb.`1 /\ lb.`1 < bound /\ lb <> (Param.l,Param.lsb)) {
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
        
        if (ib = (Param.l,Param.lsb)) {
          mask = O.f(t);
          ans = (kw2w ki lsbi, kw2w kj lsbj, mask ^ (F kj t) ^ xx);
        }
        else  {
            if (jb = (Param.l,Param.lsb)) {
              mask = O.f(t);
              ans = (kw2w ki lsbi, kw2w kj lsbj, (F ki t) ^ mask ^ xx);
           }
           else  {
              mask = O.f(t);
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
      
      (*i = 0;
      while (i < bound) {
        Param.kpub.[(i, false)] = (witness,false);
        Param.kpub.[(i, true)] = (witness,true);
        i = i + 1;
      }*)

      i = 0;
      while (i < bound) {
        if (i = Param.l) {
          Param.lsb = ${0,1};
          Param.kpub.[(i,Param.lsb)] = (witness,Param.lsb); (* can never return or encrypt this key *)
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
  
equiv true_key lp (A <:  Adv_DKC_t{Param,PRFr_Wrapped,DKCp}):
    DKCSecurity.Game(DKC_O,A).game ~
    IND(PRFr_Wrapped,D(A)).main : ={glob A} /\ 0 <= lp < boundl /\ b{1} /\ l{1} = lp /\ l{2} = lp
                               ==> ={res}.
    proof.
      proc.
      inline PRFr_Wrapped.init D(A,PRFr_Wrapped).distinguish. 
      seq 1 3 : (={glob A} /\ 0 <= lp < bound /\ b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ DKCp.ksec{1} = kw2w PRFr_Wrapped.k{2} Param.lsb{2} /\ getlsb DKCp.ksec{1} = DKCp.lsb{1} /\ lsb{1} = DKCp.lsb{1} /\ lsb{2} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})])) Param.lsb{2} /\
      (*snd (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})]) = Param.lsb{2} /\*)
      (forall k b, 0 <= k < bound => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < bound => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < bound => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))
      ); 
      inline DKC_O.initialize D(A, PRFr_Wrapped).initialize.

    splitwhile{1} 10 : i < DKCp.l. 
    splitwhile{1} 11 : i = DKCp.l.

    splitwhile{2} 10 : i < Param.l. 
    splitwhile{2} 11 : i = Param.l.
    
    wp; while (={glob A} /\ 0 <= lp < bound /\ b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ DKCp.ksec{1} = kw2w PRFr_Wrapped.k{2} Param.lsb{2} /\ getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
      Param.tbl{2} = map0 /\
      i{1} = i{2} /\ DKCp.l{1} < i{1} <= bound /\
      (*oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})] = (witness,witness) /\
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = witness /\*)
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})])) Param.lsb{2} /\
      (*snd (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})]) = Param.lsb{2} /\*)
      (forall k b, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < i{1} => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))).

    rcondf{1} 1. auto. progress => /#.
    rcondf{2} 1. auto. progress => /#.

    auto; progress; first 2 by idtac=>/#. rewrite !getP => /#. 
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. done. case ((k, b1) = (i{2}, false)) => hc'. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. done. idtac=>/#.
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. case ((k, b1) = (i{2}, false)) => hc'. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. idtac=>/#. 
        rewrite !getP => /#.

    rcondt{1} 11. auto. while (0 <= i <= DKCp.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondt{1} 11. progress. while (0 <= i <= DKCp.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondf{1} 16. progress. auto. while (0 <= i <= DKCp.l). if. auto => /#. auto => /#. wp. auto. progress;smt.
    
    rcondt{2} 11. auto. while (0 <= i <= Param.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondt{2} 11. progress. while (0 <= i <= Param.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondf{2} 16. progress. auto. while (0 <= i <= Param.l). if. auto => /#. auto => /#. wp. auto. progress;smt.

    swap{2} 1 10.
    wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (!Param.lsb{2})). wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (Param.lsb{2})). rnd.

    while (={glob A} /\ 0 <= lp < bound /\ b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\
      i{1} = i{2} /\ 0 <= i{1} <= DKCp.l{1} /\

      (forall k b, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < i{1} => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2})) ).

    rcondf{1} 1. auto. progress => /#.
    rcondf{2} 1. auto. progress => /#.

    auto. progress; first 2 by idtac=>/#.  
    rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. done. case ((k, b1) = (i{2}, false)) => hc'. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. done. idtac=>/#.
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. case ((k, b1) = (i{2}, false)) => hc'. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. idtac=>/#. 
        rewrite !getP => /#.  

    auto; progress; last 3 by idtac=>/#.
        by smt. 
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite w2kw'_kw2w'. 
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w' kR (lsbL)) = lsbL <=> true. simplify kw2w'. rewrite get_setlsb. done. done. 
        by smt.
        rewrite kw2w'_w2kw'. by rewrite (Dword.lsb_dwordLsb (lsbL) _). done.  
        by rewrite w2kw'_kw2w'. 
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w' kiR (!lsbL)) = !lsbL <=> true. simplify kw2w'. rewrite get_setlsb. done. done. 
        by smt.
        rewrite kw2w'_w2kw'. by rewrite (Dword.lsb_dwordLsb (!lsbL) _). done.  
        rewrite kw2w_w2kw'. by rewrite (Dword.lsb_dwordLsb (lsbL) _). done.  
        by rewrite (Dword.lsb_dwordLsb (lsbL) _). 
        by idtac=>/#.
        by idtac=>/#.
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        rewrite !getP. case ((l{1}, !lsbL) = (i_R, !lsbL)) => hc. rewrite !oget_some. smt. case ((l{1}, !lsbL) = (i_R, lsbL)) => hc'. smt. idtac=>/#. 

        wp. 

    call (_: 
  0 <= lp < bound /\
  DKCp.used{1} = Param.used{2} /\
  DKCp.b{1} /\
  DKCp.l{1} = Param.l{2} /\
  DKCp.l{1} = lp /\
  DKCp.lsb{1} = Param.lsb{2} /\
  DKCp.ksec{1} = kw2w PRFr_Wrapped.k{2} Param.lsb{2} /\
  getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
  Param.tbl{2} = map0 /\
  oget DKCp.kpub{1}.[(DKCp.l{1}, DKCp.lsb{1})] =
        kw2w (fst (oget Param.kpub{2}.[(Param.l{2}, Param.lsb{2})])) Param.lsb{2} /\
  (forall (k : int) (b0 : bool),
     0 <= k < bound =>
     k <> Param.l{2} =>
     oget DKCp.kpub{1}.[(k, b0)] =
     kw2w (fst (oget Param.kpub{2}.[(k, b0)])) b0) /\
  (forall (k : int) (b0 : bool),
     0 <= k < bound =>
     snd (oget Param.kpub{2}.[(k, b0)]) = b0) /\
  (forall (k : int),
    0 <= k < bound =>
    k = Param.l{2} =>
    oget DKCp.kpub{1}.[(k, !Param.lsb{2})] =
    kw2w (fst (oget Param.kpub{2}.[(k, !Param.lsb{2})])) (!Param.lsb{2}))).

    proc.
    case (! mem DKCp.used{1} q{1}.`5 /\ 0 <= q{1}.`2.`1 /\
    q{1}.`2.`1 < q{1}.`3.`1 /\       
    q{1}.`3.`1 < q{1}.`4.`1 /\  q{1}.`4.`1 < bound /\                
    q{1}.`4 <> (DKCp.l{1}, DKCp.lsb{1})); last first.

      rcondf{1} 3; first by auto.
      rcondf{2} 3; first by auto.   
      by auto.

      rcondt{1} 3; first by auto. 
      rcondt{2} 3; first by auto.
 
      case (q{1}.`1).
        rcondt{1} 8; first by auto => /#. 
        rcondt{2} 8; first by auto. 

    case (q{2}.`2 = (Param.l{2}, Param.lsb{2})).
        rcondt{2} 9. progress. auto. 
        inline PRFr_Wrapped.f. 
        wp. rnd. wp. skip. progress. 
          by rewrite H14 H3 => /#.   

          cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H4 => /#. 
          simplify PrfDKC.E. simplify PRF.F. rewrite H14 /=. congr. congr. congr. rewrite w2kw_kw2w => /#. cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. 

    case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondf{2} 9. progress. auto. rcondt{2} 9. progress. auto. 
        inline PRFr_Wrapped.f.
        wp. rnd. wp. skip. progress.
        cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4 => /#.
        by rewrite H15 H3 => /#. 
        simplify PrfDKC.E. simplify PRF.F. cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. rewrite H15 /=. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. rewrite w2kw_kw2w => /#. 

    rcondf{2} 9. progress. auto. 
    rcondf{2} 9. auto.
    inline PRFr_Wrapped.f.
    wp. rnd. wp. skip. progress.
      by idtac=>/#.
      by idtac=>/#.
      cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. 


    (********************)
    (* !rn *)
    (********************)

    rcondf{1} 8. progress. auto. progress. idtac=>/#.
    rcondf{2} 8. progress. auto.

    case (q{2}.`2 = (Param.l{2}, Param.lsb{2})).
        rcondt{2} 8. progress. auto. 
        inline PRFr_Wrapped.f. 
        wp. skip. progress. 
        by rewrite H14 H3 => /#.   

          cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H4 => /#.
          simplify PrfDKC.E. simplify PRF.F. rewrite H14 /=. congr. congr. congr. rewrite w2kw_kw2w => /#. cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. cut ->: q{2}.`4 = (q{2}.`4.`1,q{2}.`4.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. idtac=>/#.

    case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondf{2} 8. progress. auto. rcondt{2} 8. progress. auto. 
        inline PRFr_Wrapped.f.
        wp. skip. progress. 
        cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4 => /#.
        by rewrite H15 H3 => /#. 
        simplify PrfDKC.E. simplify PRF.F. cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. rewrite H15 /=. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. rewrite w2kw_kw2w => /#. idtac=>/#.

    rcondf{2} 8. progress. auto. 
    rcondf{2} 8. auto.
    inline PRFr_Wrapped.f. 
    wp. skip. progress.
      by idtac=>/#.
      by idtac=>/#.
      cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. idtac=>/#.

  skip. progress => /#.
  qed.

  lemma aux_xorwK (w w1 w2:word): w = w ^ w1 ^ w2 ^ w1 ^ w2 by []. 
  lemma aux_xorwK' (w w1 w2 w3:word): w1 ^ w2 ^ w = w3 ^ w2 ^ (w ^ w1 ^ w3) by [].
      
equiv false_key lp (A <:  Adv_DKC_t{Param,DKCp,PRFr_Wrapped,RandomFunction}):
    DKCSecurity.Game(DKC_O,A).game ~
    IND(RandomFunction,D(A)).main : ={glob A} /\ 0 <= lp < boundl /\ !b{1} /\ l{1} = lp /\ l{2} = lp
                               ==> res{1} <> res{2}.

    proof.
      proc. 
      inline PRFr_Wrapped.init RandomFunction.init D(A, RandomFunction).distinguish.
      seq 1 3 : (={glob A} /\ 0 <= lp < bound /\ !b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ !DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ lsb{1} = DKCp.lsb{1} /\ lsb{2} = Param.lsb{2} /\ getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
      Param.tbl{2} = map0 /\
      RandomFunction.m{2} = map0 /\
      (*oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})] = (witness,witness) /\
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = witness /\*)
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})])) Param.lsb{2} /\
      (*snd (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})]) = Param.lsb{2} /\*)
      (forall k b, 0 <= k < bound => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < bound => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < bound => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))



    );   
      inline DKC_O.initialize D(A, RandomFunction).initialize.

        splitwhile{1} 10 : i < DKCp.l. 
    splitwhile{1} 11 : i = DKCp.l.

    splitwhile{2} 10 : i < Param.l. 
    splitwhile{2} 11 : i = Param.l.
    
        wp; while (={glob A} /\ 0 <= lp < bound /\ !b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ !DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
      Param.tbl{2} = map0 /\
      i{1} = i{2} /\ DKCp.l{1} < i{1} <= bound /\
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})])) Param.lsb{2} /\
      (forall k b, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < i{1} => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))).
        
        rcondf{1} 1. auto. progress => /#.
    rcondf{2} 1. auto. progress => /#.

    auto; progress; first 2 by idtac=>/#. rewrite !getP => /#. 
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. done. case ((k, b1) = (i{2}, false)) => hc'. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. done. idtac=>/#.
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. case ((k, b1) = (i{2}, false)) => hc'. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. idtac=>/#. 
        rewrite !getP => /#. 


    rcondt{1} 11. auto. while (0 <= i <= DKCp.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondt{1} 11. progress. while (0 <= i <= DKCp.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondf{1} 16. progress. auto. while (0 <= i <= DKCp.l). if. auto => /#. auto => /#. wp. auto. progress;smt.
    
    rcondt{2} 11. auto. while (0 <= i <= Param.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondt{2} 11. progress. while (0 <= i <= Param.l). if. auto => /#. auto => /#. wp. auto. progress;smt. rcondf{2} 16. progress. auto. while (0 <= i <= Param.l). if. auto => /#. auto => /#. wp. auto. progress;smt.

    wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (!Param.lsb{2})). wp. rnd{1}. rnd.
    
    while (={glob A} /\ 0 <= lp < bound /\ !b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ !DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\
      i{1} = i{2} /\ 0 <= i{1} <= DKCp.l{1} /\
      (forall k b, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < i{1} => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))).

    rcondf{1} 1. auto. progress => /#.
    rcondf{2} 1. auto. progress => /#.

    auto. progress; first 2 by idtac=>/#.  
    rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. done. case ((k, b1) = (i{2}, false)) => hc'. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. done. idtac=>/#.
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. case ((k, b1) = (i{2}, false)) => hc'. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. idtac=>/#. 
        rewrite !getP => /#.  
    
    auto; progress; last 3 by idtac=>/#.
        by smt.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite Dword.dwordLsb_lossless. 
        by rewrite w2kw'_kw2w'.
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w' kiR (!lsbL)) = !lsbL <=> true. simplify kw2w'. rewrite get_setlsb. done. done. 
        by smt.
        rewrite kw2w'_w2kw'. rewrite (Dword.lsb_dwordLsb (!lsbL) _). done. done. done.
        rewrite (Dword.lsb_dwordLsb (lsbL) _). done. done.
        by idtac=>/#.
        by idtac=>/#.
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        rewrite !getP. case ((l{1}, !lsbL) = (i_R, !lsbL)) => hc. rewrite !oget_some. smt. case ((l{1}, !lsbL) = (i_R, lsbL)) => hc'. smt. idtac=>/#. 
    wp.

    call (_ : 
  0 <= lp < bound /\
  DKCp.used{1} = Param.used{2} /\
  !DKCp.b{1} /\
  DKCp.l{1} = Param.l{2} /\
  DKCp.l{1} = lp /\
  DKCp.lsb{1} = Param.lsb{2} /\
  getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
  oget DKCp.kpub{1}.[(DKCp.l{1}, DKCp.lsb{1})] =
  kw2w (fst (oget Param.kpub{2}.[(Param.l{2}, Param.lsb{2})])) Param.lsb{2} /\
  DKCp.used{1} = dom (RandomFunction.m{2}) /\    
  (forall (k : int) (b0 : bool),
     0 <= k < bound =>
     k <> Param.l{2} =>
     oget DKCp.kpub{1}.[(k, b0)] =
     kw2w (fst (oget Param.kpub{2}.[(k, b0)])) b0) /\
  (forall (k : int) (b0 : bool),
     0 <= k < bound => snd (oget Param.kpub{2}.[(k, b0)]) = b0) /\
  (forall (k : int),
    0 <= k < bound =>
    k = Param.l{2} =>
    oget DKCp.kpub{1}.[(k, !Param.lsb{2})] =
    kw2w (fst (oget Param.kpub{2}.[(k, !Param.lsb{2})])) (!Param.lsb{2}))).

    proc.
    
    case (! mem DKCp.used{1} q{1}.`5 && 0 <= q{1}.`2.`1 /\       
    q{1}.`2.`1 < q{1}.`3.`1 /\                 
    q{1}.`3.`1 < q{1}.`4.`1 /\      q{1}.`4.`1 < bound /\             
    q{1}.`4 <> (DKCp.l{1}, DKCp.lsb{1})); last first.

      rcondf{1} 3; first by auto => /#. 
      rcondf{2} 3; first by auto => /#. 
      by auto.

      rcondt{1} 3; first by auto. 
      rcondt{2} 3; first by auto.
 
      case (q{1}.`1).
        rcondt{1} 8. auto => /#. 
        rcondt{2} 8. auto. 

    case (q{2}.`2 = (Param.l{2}, Param.lsb{2})).
        rcondt{2} 9. progress. auto. 
        inline RandomFunction.f.
        rcondt{2} 10. auto.  
    swap{2} 8 3. wp. rnd (fun w, w ^ (F (fst (w2kw aa{1})) t{1}) ^ mask{2}). wp. rnd{2}. wp. skip. progress. 
      by smt. 
      by rewrite H13 /= -aux_xorwK.  
      by rewrite !Dword.mu_x_def. 
      by rewrite H13 /= Dword.in_supp_def.
      by rewrite H13 /= -aux_xorwK.
      by rewrite H13 H2 => /#.   
      cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H3 => /#.
      simplify PrfDKC.E fst; rewrite H13 /= getP /= oget_some -aux_xorwK'; smt. 
      by rewrite dom_set.

    case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondf{2} 9. progress. auto. rcondt{2} 9. progress. auto.
        inline RandomFunction.f.
        rcondt{2} 10. auto.  
    swap{2} 8 3. wp. rnd (fun w, w ^ (F (fst (w2kw bb{1})) t{1}) ^ mask{2}). wp. rnd{2}. wp. skip. progress. 
      by smt. 
      by rewrite -aux_xorwK.  
      by rewrite !Dword.mu_x_def. 
      by rewrite Dword.in_supp_def.
      by rewrite -aux_xorwK.
      cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H3 => /#.
      by rewrite H14 H2 => /#.         
      cut ->: q{2}.`2 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. simplify PrfDKC.E fst; rewrite H14 /= getP /= oget_some; smt tmo=10. 
      by rewrite dom_set.  

      rcondf{2} 9. progress. auto. rcondf{2} 9. progress. auto.
      inline RandomFunction.f.
      rcondt{2} 10. auto.  
    wp. rnd{2}. wp. rnd. wp. skip. progress. 
      by smt. 
      cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. smt tmo=10.
      cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. smt tmo=10. 
      cut ->: q{2}.`2 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. 
      by rewrite dom_set.  

  rcondf{2} 8. auto. 
  case (q{2}.`2 = (Param.l{2}, Param.lsb{2})).
        rcondt{1} 8. auto. progress => /#. 
        rcondt{2} 8. progress. auto. 
        inline RandomFunction.f.
        rcondt{2} 9. auto.  
    wp. rnd (fun w, w ^ (F (fst (w2kw aa{1})) t{1}) ^ xx{2}). wp. skip. progress. 
      by rewrite H13 /= -aux_xorwK.  
      by rewrite !Dword.mu_x_def. 
      by rewrite H13 /= Dword.in_supp_def.
      by rewrite H13 /= -aux_xorwK.
      by rewrite H13 H2 => /#.   
      cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H3 => /#.
      simplify PrfDKC.E fst; rewrite H13 /= getP /= oget_some;smt.  
      by rewrite dom_set.

  case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondt{1} 8. auto. progress => /#. 
        rcondf{2} 8. auto. rcondt{2} 8. auto.
        inline RandomFunction.f.
        rcondt{2} 9. auto.  
    wp. rnd (fun w, w ^ (F (fst (w2kw bb{1})) t{1}) ^ xx{2}). wp. skip. progress. 
      by rewrite H13 /= -aux_xorwK.  
      by rewrite !Dword.mu_x_def. 
      by rewrite H13 /= Dword.in_supp_def.
      by rewrite H13 /= -aux_xorwK.
      cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H3 => /#.
      by rewrite H14 H2 => /#.   
      cut ->: q{2}.`2 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. simplify PrfDKC.E fst; rewrite H14 /= getP /= oget_some;smt.  
      by rewrite dom_set.

    rcondf{1} 8. auto. progress => /#. 
        rcondf{2} 8. auto. rcondf{2} 8. auto.
        inline RandomFunction.f.
        rcondt{2} 9. auto.  
    wp. rnd{2}. wp. skip. progress. 
      by smt.
      cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. idtac=>/#. 
      cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. smt tmo=10.  
      cut ->: q{2}.`2 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. simplify. cut ->: q{2}.`4 = (q{2}.`4.`1,q{2}.`4.`2) by idtac=>/#. case (q{2}.`4.`1 = Param.l{2}) => hc. cut ->: q{2}.`4.`2 = ! getlsb DKCp.ksec{1} by idtac=>/#. rewrite H5 => /#. rewrite H3 => /#.
      by rewrite dom_set.  
    
skip. progress. by rewrite dom0. idtac=>/#. 
  qed.
    
lemma PrfDKC_secure (A <: Adv_DKC_t{PRFr_Wrapped,DKCp,Param,RandomFunction}) &m i: 0 <= i < boundl =>
    Pr[DKCSecurity.Game(DKC_O,A).game(true,i)@ &m:res] - 
    Pr[DKCSecurity.Game(DKC_O,A).game(false,i)@ &m:!res] =
    Pr[IND(PRFr_Wrapped,D(A)).main(i)@ &m:res] - Pr[IND(RandomFunction,D(A)).main(i)@ &m:res].
  proof.
    move => hi.
    congr.
    byequiv (true_key (i) A). done. done.
    congr. byequiv (false_key (i) A). done. smt. 
qed.
  
end SomeDKC.
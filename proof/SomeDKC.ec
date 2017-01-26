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

  (*************************************)
  (** AUXLIAR FUNCTIONS *)
  (*************************************)
  
  op kw2w(kw,lsb) =
  if kw = witness then witness else
                   let lsbi = if lsb then 1 else 0
                      in let kwi = (KW.to_int kw) * 2 + lsbi
                      in W.setlsb (W.from_int kwi) lsb.

  op kw2w'(kw,lsb) =
                   let lsbi = if lsb then 1 else 0
                      in let kwi = (KW.to_int kw) * 2 + lsbi
                      in W.setlsb (W.from_int kwi) lsb.
  
  op w2kw(w) =
  if w = witness then (witness,W.getlsb w) else
  let kwi = (W.to_int w) %/ 2 (* / 2 *)
                          in let lsbi = W.getlsb w
                          in (KW.from_int kwi,lsbi).

  op w2kw'(w) =
  let kwi = (W.to_int w) %/ 2 (* / 2 *)
                          in let lsbi = W.getlsb w
                          in (KW.from_int kwi,lsbi).
  
  lemma w2kw_kw2w w b : fst (w2kw (kw2w w b)) = w. 
  proof.
    simplify w2kw kw2w fst.
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
  
  (*op w2kw'(w) =
  (*if w = witness then witness else*)
  let kwi = (W.to_int w) %/ 2 (* / 2 *)
                          in let lsbi = W.getlsb w
                          in KW.from_int kwi.*)
  
  clone import SomePRF.PRF with
	type D = word,
	type R = word,
	type K = KW.word,
        op dK = KW.Dword.dword.
          
  clone import DKC.DKCScheme as PrfDKC with
        type tweak_t = word,
        type msg_t = word,
        type key1_t = word,
        type key2_t = word,
        type cipher_t = word,
        op E(t,k1,k2,m) = (F (fst (w2kw k1)) t) ^ (F (fst (w2kw k2)) t) ^ m,
        op D(t,k1,k2,c) = (F (fst (w2kw k1)) t) ^ (F (fst (w2kw k2)) t) ^ c.
        
  (*prover ["Z3"].*)
        
  (** DKC security definitions, instantiated with the words defined in W *)
  clone import DKCSec2.DKCSecurity with
    (*theory WD <- W,*)
        theory DKCScheme <- PrfDKC.
  

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
  
  (*************************************)
  (** DKC PART *)
  (*************************************)
  
  (** DKC parameters *)
  module DKCp = {
    var b : bool
    var ksec : word
    var kpub : ((int * bool), word) fmap
    var used : word fset
    var lsb : bool
    var l : int
  }.

  op itb (x:int) = if x = 1 then true else false.
  
  module DKC_O : DKC_AdvOracles = {    
    
    proc initialize(b : bool,l:int): bool = {
      var i, tok1, tok2;
      
      DKCp.b = b;
      DKCp.l = l;
      DKCp.lsb = witness;
      DKCp.used = FSet.fset0;
      DKCp.kpub = map0;
      
      i = 0;
      while (i < bound) {
        DKCp.kpub.[(i, false)] = W.zeros;
        DKCp.kpub.[(i, true)] = W.zeros;
        i = i + 1;
      }
            
      i = 0;
      while (i < bound) {
        if (i = DKCp.l) {
          DKCp.lsb = ${0,1};
          DKCp.kpub.[(i,DKCp.lsb)] = witness; (* can never return or encrypt this key *)
          DKCp.kpub.[(i,!DKCp.lsb)] = $Dword.dwordLsb (!DKCp.lsb);  
        }
        else {
          tok1 = $Dword.dwordLsb (false);
          tok2 = $Dword.dwordLsb (true);
            DKCp.kpub.[(i, false)] = tok1;
            DKCp.kpub.[(i, true)] = tok2;
        }
        i = i + 1;
      }

      DKCp.ksec = $Dword.dwordLsb (DKCp.lsb);
      
      return DKCp.lsb;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb,xx : word;
      var ib,jb,lb : int * bool;
      var bi,bj,bl', rn: bool;
      var t, ki, kj : word;
      var ans : answer_DKC;

      ans = bad;
      (rn,ib,jb,lb,t) = q;
      
      if (!(mem DKCp.used t) && 0 <= ib.`1 /\ ib.`1 < jb.`1 && jb.`1 < lb.`1 && lb.`1 < bound /\ lb <> (DKCp.l,DKCp.lsb)) {
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
  
      if (!(mem Param.used t) && 0 <= ib.`1 /\ ib.`1 < jb.`1 && jb.`1 < lb.`1 && lb.`1 < bound /\ lb <> (Param.l,Param.lsb)) {
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
      
  
equiv true_key lp (A <:  Adv_DKC_t{Param,DKCp,PRFr_Wrapped}):
    DKCSecurity.Game(DKC_O,A).game ~
    IND(PRFr_Wrapped,D(A)).main : ={glob A} /\ 0 <= lp < bound /\ b{1} /\ l{1} = lp /\ l{2} = lp
                               ==> ={res}.
    proof.
      proc.
      inline PRFr_Wrapped.init D(A,PRFr_Wrapped).distinguish. 
      seq 1 3 : (={glob A} /\ 0 <= lp < bound /\ b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ DKCp.ksec{1} = kw2w PRFr_Wrapped.k{2} Param.lsb{2} /\ getlsb DKCp.ksec{1} = DKCp.lsb{1} /\ lsb{1} = DKCp.lsb{1} /\ lsb{2} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\

      (*oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})] = (witness,witness) /\
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = witness /\*)
      oget DKCp.kpub{1}.[(DKCp.l{1},DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})])) Param.lsb{2} /\
      (*snd (oget Param.kpub{2}.[(Param.l{2},Param.lsb{2})]) = Param.lsb{2} /\*)
      (forall k b, 0 <= k < bound => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (forall k b, 0 <= k < bound => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < bound => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))



    );   
      inline DKC_O.initialize D(A, PRFr_Wrapped).initialize.

        swap{2} 1 11.
        wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (Param.lsb{2})).
    
        wp; while (={glob A} /\ 0 <= lp < bound /\ b{1} /\ ={i} /\ 0 <= i{1} <= bound /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ 
        Param.tbl{2} = map0 /\
      (*(forall k, 0 <= k < i{1} => k = Param.l{2} => oget Param.kpub{2}.[(k,Param.lsb{2})] = (witness,witness)) /\
      (forall k, 0 <= k < i{1} => k = DKCp.l{1} => oget DKCp.kpub{1}.[(k,DKCp.lsb{1})] = witness) /\*)
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(k,Param.lsb{2})])) Param.lsb{2}) /\
      (forall k b, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (*(forall k, 0 <= k < i{1} => k = Param.l{2} => snd (oget Param.kpub{2}.[(k,Param.lsb{2})]) = Param.lsb{2}) /\*)
      (forall k b, 0 <= k < i{1} => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))).
        
        if; first by progress. 
        wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (!Param.lsb{2})). wp. rnd. skip; progress.
        (*by rewrite Dword.dwordLsb_lossless.*)
        by rewrite w2kw'_kw2w'.  
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w' kiR (!lsbL)) = !lsbL <=> true. simplify kw2w'. rewrite get_setlsb. done. done.
        by smt.
        rewrite kw2w'_w2kw'. rewrite (Dword.lsb_dwordLsb (!lsbL) _). done. done. done. 
        idtac=>/#.
        idtac=>/#.
        rewrite !getP => /#. 
        rewrite !getP => /#.  
        rewrite !getP => /#. 
        rewrite !getP ;smt.  

    
      auto; progress; first 2 by idtac=>/#. rewrite !getP => /#. 
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. done. case ((k, b1) = (i{2}, false)) => hc'. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. done. idtac=>/#.
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. case ((k, b1) = (i{2}, false)) => hc'. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. idtac=>/#. 
        rewrite !getP => /#. 

    wp; while (={glob A} /\ 0 <= lp < bound /\ b{1} /\ ={i} /\ 0 <= i{1} <= bound /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\ 
      (forall k, 0 <= k < i{1} => oget DKCp.kpub{1}.[(k,false)] = W.zeros) /\
      (forall k, 0 <= k < i{1} => oget DKCp.kpub{1}.[(k,true)] = W.zeros) /\
      (forall k, 0 <= k < i{1} => oget Param.kpub{2}.[(k,false)] = (KW.zeros, false)) /\
      (forall k, 0 <= k < i{1} => oget Param.kpub{2}.[(k,true)] = (KW.zeros, true))).
      auto; progress; expect 6 by by rewrite ?getP => /#. 

    auto; progress; last 3 by idtac=>/#.
        by smt. 
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by smt.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#. 
        by rewrite w2kw'_kw2w'. 
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w' kR (lsb_R)) = lsb_R <=> true. simplify kw2w'. rewrite get_setlsb. done. done. 
        by smt.
        rewrite kw2w'_w2kw'. by rewrite (Dword.lsb_dwordLsb (lsb_R) _). done.  
        rewrite kw2w_w2kw'. by rewrite (Dword.lsb_dwordLsb (lsb_R) _). done.  
        by rewrite (Dword.lsb_dwordLsb (lsb_R) _).  
        rewrite H22 => /#. 
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
      (*snd (oget Param.kpub{2}.[(Param.l{2}, Param.lsb{2})]) = Param.lsb{2} /\*)
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
    case (! mem DKCp.used{1} q{1}.`5 && 0 <= q{1}.`2.`1 /\       
    q{1}.`2.`1 < q{1}.`3.`1 &&                 
    q{1}.`3.`1 < q{1}.`4.`1 &&      q{1}.`4.`1 < bound /\             
    q{1}.`4 <> (DKCp.l{1}, DKCp.lsb{1})); last first.

      rcondf{1} 3; first by auto. 
      rcondf{2} 3; first by auto. 
      by auto.

      rcondt{1} 3; first by auto. 
      rcondt{2} 3; first by auto.
 
      case (q{1}.`1).
        rcondt{1} 8. auto => /#. 
        rcondt{2} 8. auto. 

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
    (*case (q{2}.`2.`1 = Param.l{2}).*)    

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
          simplify PrfDKC.E. simplify PRF.F. rewrite H14 /=. congr. congr. congr. rewrite w2kw_kw2w => /#. cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. idtac=>/#.

    case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondf{2} 8. progress. auto. rcondt{2} 8. progress. auto. 
        inline PRFr_Wrapped.f.
        wp. skip. progress.
        cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4 => /#.
        by rewrite H15 H3 => /#. 
        simplify PrfDKC.E. simplify PRF.F. cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. rewrite H15 /=. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. rewrite w2kw_kw2w => /#. idtac=>/#.

    rcondf{2} 8. progress. auto. 
    rcondf{2} 8. auto.
    (*case (q{2}.`2.`1 = Param.l{2}).*)    

    wp. skip. progress.
      by idtac=>/#.
      by idtac=>/#.
      cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. idtac=>/#.

  skip. progress => /#.
  qed.
  
equiv false_key lp (A <:  Adv_DKC_t{Param,DKCp,PRFr_Wrapped,RandomFunction}):
    DKCSecurity.Game(DKC_O,A).game ~
    IND(RandomFunction,D(A)).main : ={glob A} /\ 0 <= lp < bound /\ !b{1} /\ l{1} = lp /\ l{2} = lp
                               ==> ={res}.

    proof.
      proc. 
      inline PRFr_Wrapped.init RandomFunction.init D(A, RandomFunction).distinguish DKC_O.initialize. swap{1} 13 -1.
      seq 12 3 : (={glob A} /\ 0 <= lp < bound /\ !b{1} /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ !DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ lsb{1} = DKCp.lsb{1} /\ lsb{2} = Param.lsb{2} /\ (*getlsb DKCp.ksec{1} = DKCp.lsb{1} /\*)
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
        
    
        (*swap{2} 1 11.
        wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (Param.lsb{2})).*)
    
        wp; while (={glob A} /\ 0 <= lp < bound /\ !b{1} /\ ={i} /\ 0 <= i{1} <= bound /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ !DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\ 
        Param.tbl{2} = map0 /\ 
      (*(forall k, 0 <= k < i{1} => k = Param.l{2} => oget Param.kpub{2}.[(k,Param.lsb{2})] = (witness,witness)) /\
      (forall k, 0 <= k < i{1} => k = DKCp.l{1} => oget DKCp.kpub{1}.[(k,DKCp.lsb{1})] = witness) /\*)
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,DKCp.lsb{1})] = kw2w (fst (oget Param.kpub{2}.[(k,Param.lsb{2})])) Param.lsb{2}) /\
      (forall k b, 0 <= k < i{1} => k <> Param.l{2} => oget DKCp.kpub{1}.[(k,b)] = kw2w (fst (oget Param.kpub{2}.[(k,b)])) b) /\
      (*(forall k, 0 <= k < i{1} => k = Param.l{2} => snd (oget Param.kpub{2}.[(k,Param.lsb{2})]) = Param.lsb{2}) /\*)
      (forall k b, 0 <= k < i{1} => snd (oget Param.kpub{2}.[(k,b)]) = b) /\
      (forall k, 0 <= k < i{1} => k = Param.l{2} => oget DKCp.kpub{1}.[(k,!Param.lsb{2})] = kw2w (fst (oget Param.kpub{2}.[(k,!Param.lsb{2})])) (!Param.lsb{2}))).
        
        if; first by progress. 
        wp. rnd (fun w, fst (w2kw' w)) (fun w, kw2w' w (!Param.lsb{2})). wp. rnd. skip; progress.
        (*by rewrite Dword.dwordLsb_lossless.*)
        by rewrite w2kw'_kw2w'.  
        rewrite KW.Dword.mu_x_def Dword.dwordLsb_mu_x. cut ->: getlsb (kw2w' kiR (!lsbL)) = !lsbL <=> true. simplify kw2w'. rewrite get_setlsb. done. done.
        by smt.
        rewrite kw2w'_w2kw'. rewrite (Dword.lsb_dwordLsb (!lsbL) _). done. done. done. 
        idtac=>/#.
        idtac=>/#.
        rewrite !getP => /#. 
        rewrite !getP => /#.  
        rewrite !getP => /#. 
        rewrite !getP ;smt.  

    
      auto; progress; first 2 by idtac=>/#. rewrite !getP => /#. 
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. done. case ((k, b1) = (i{2}, false)) => hc'. rewrite !oget_some kw2w_w2kw. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. done. idtac=>/#.
        rewrite !getP. case ((k, b1) = (i{2}, true)) => hc. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (true) _). done. idtac=>/#. case ((k, b1) = (i{2}, false)) => hc'. rewrite oget_some. simplify w2kw snd. rewrite (Dword.lsb_dwordLsb (false) _). done. idtac=>/#. idtac=>/#. 
        rewrite !getP => /#. 

    wp; while (={glob A} /\ 0 <= lp < bound /\ !b{1} /\ ={i} /\ 0 <= i{1} <= bound /\ (b{1}, l{1}).`2 = lp /\ l{2} = lp /\
      DKCp.used{1} = Param.used{2} /\ DKCp.used{1} = fset0 /\ DKCp.b{1} = b{1} /\ !DKCp.b{1} /\
      DKCp.l{1} = Param.l{2} /\ DKCp.l{1} = lp /\ Param.l{2} = l0{2} /\ DKCp.l{1} = l{1} /\
      DKCp.lsb{1} = Param.lsb{2} /\
      Param.tbl{2} = map0 /\ 
      (forall k, 0 <= k < i{1} => oget DKCp.kpub{1}.[(k,false)] = W.zeros) /\
      (forall k, 0 <= k < i{1} => oget DKCp.kpub{1}.[(k,true)] = W.zeros) /\
      (forall k, 0 <= k < i{1} => oget Param.kpub{2}.[(k,false)] = (KW.zeros, false)) /\
      (forall k, 0 <= k < i{1} => oget Param.kpub{2}.[(k,true)] = (KW.zeros, true))).
      auto; progress; expect 6 by by rewrite ?getP => /#. 

    auto; progress; last 3 by idtac=>/#.
        by smt. 
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by rewrite map0P =>/#.
        by smt.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#. 
        rewrite H22 => /#. 
        wp. 

    call (_ : 
  0 <= lp < bound /\
  DKCp.used{1} = Param.used{2} /\
  !DKCp.b{1} /\
  DKCp.l{1} = Param.l{2} /\
  DKCp.l{1} = lp /\
  DKCp.lsb{1} = Param.lsb{2} /\
  getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
  getlsb DKCp.ksec{1} = DKCp.lsb{1} /\
  oget DKCp.kpub{1}.[(DKCp.l{1}, DKCp.lsb{1})] =
  kw2w (fst (oget Param.kpub{2}.[(Param.l{2}, Param.lsb{2})])) Param.lsb{2} /\
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
    q{1}.`2.`1 < q{1}.`3.`1 &&                 
    q{1}.`3.`1 < q{1}.`4.`1 &&      q{1}.`4.`1 < bound /\             
    q{1}.`4 <> (DKCp.l{1}, DKCp.lsb{1})); last first.

      rcondf{1} 3; first by auto. 
      rcondf{2} 3; first by auto. 
      by auto.

      rcondt{1} 3; first by auto. 
      rcondt{2} 3; first by auto.
 
      case (q{1}.`1).
        rcondt{1} 8. auto => /#. 
        rcondt{2} 8. auto. 

    case (q{2}.`2 = (Param.l{2}, Param.lsb{2})).
        rcondt{2} 9. progress. auto. 
        inline RandomFunction.f.
        rcondt{2} 10. auto.  progress. admit. 
        wp. rnd{2} (fun w, fst (w2kw' w)) (fun w, kw2w' w (!Param.lsb{2})). wp. rnd. wp. skip. progress. 
          by smt.
          by rewrite H13 H2 => /#.   

          cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H3 => /#.
          simplify PrfDKC.E. simplify PRF.F. rewrite H13 /=. rewrite getP. simplify. rewrite oget_some. admit. cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H3. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. 

    case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondf{2} 9. progress. auto. rcondt{2} 9. progress. auto. 
        inline RandomFunction.f.
        rcondt{2} 10. auto.  progress. admit.
        wp. rnd{2}. wp. rnd. wp. skip. progress.
        by smt.
        cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H3 => /#.
        by rewrite H14 H2 => /#. 
        simplify PrfDKC.E. simplify PRF.F. cut ->: q{2}.`2 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. rewrite H14 /=. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H3. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. admit. 

    rcondf{2} 9. progress. auto. 
    rcondf{2} 9. auto.

    wp. rnd. wp. skip. progress.
      by idtac=>/#.
      by idtac=>/#.
      cut ->: q{2}.`2 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, getlsb DKCp.ksec{1}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. 


    (********************)
    (* !rn *)
    (********************)

    case (q{2}.`2 = (Param.l{2}, Param.lsb{2})).

    rcondt{1} 8. progress. auto. progress. idtac=>/#. 
    rcondf{2} 8. progress. auto.

    
        rcondt{2} 8. progress. auto. 
        inline RandomFunction.f.
        rcondt{2} 9. auto.  progress. admit.
        wp. rnd{1}. rnd{2}. wp. skip. progress. 
        by smt. by smt. by rewrite H13 H2 => /#.   

          cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H3 => /#.
          simplify PrfDKC.E. simplify PRF.F. rewrite H13 /=. congr. congr. admit. congr. cut ->: q{2}.`3 = (q{2}.`3.`1,q{2}.`3.`2) by idtac=>/#. rewrite H3. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. admit. 

    case (q{2}.`3 = (Param.l{2}, Param.lsb{2})).
        rcondt{1} 8. progress. auto. progress. idtac=>/#. 
    rcondf{2} 8. progress. auto.
        rcondf{2} 8. progress. auto. rcondt{2} 8. progress. auto. 
        inline RandomFunction.f. rcondt{2} 9. auto.  progress. admit.
        wp. rnd{1}skip. progress.
        cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4 => /#.
        by rewrite H15 H3 => /#. 
        simplify PrfDKC.E. simplify PRF.F. cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. rewrite H15 /=. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. rewrite H4. idtac=>/#. idtac=>/#. rewrite w2kw_kw2w =>/#. rewrite w2kw_kw2w => /#. idtac=>/#.

    rcondf{2} 8. progress. auto. 
    rcondf{2} 8. auto.
    (*case (q{2}.`2.`1 = Param.l{2}).*)    

    wp. skip. progress.
      by idtac=>/#.
      by idtac=>/#.
      cut ->: q{2}.`2 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. cut ->: q{2}.`3 = (Param.l{2}, Param.lsb{2}) <=> false by idtac=>/#. simplify. simplify E. congr. congr. congr. cut ->: q{2}.`2 = (q{2}.`2.`1,q{2}.`2.`2) by idtac=>/#. by smt. by smt. idtac=>/#.




  qed.

    
lemma PrfDKC_secure : forall (A <: Adv_DKC_t) &m i, 0 <= i < bound =>
    Pr[DKCSecurity.Game(DKC,A).game(true,i)@ &m:res] - 
    Pr[DKCSecurity.Game(DKC,A).game(false,i)@ &m:!res] =
    Pr[IND(PRFr_Wrapped,D(A)).main(i)@ &m:res] - Pr[IND(RandomFunction,D(A)).main(i)@ &m:!res].
    admit.
  qed.

  
end SomeDKC.
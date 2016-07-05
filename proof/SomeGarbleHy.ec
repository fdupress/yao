require import Real.
require import Int.
require import IntDiv.
require import FSet.
require import NewFMap.
require import Array.
require import Distr.
require import Bool.
require import Pair.
require import DInterval.
require import Option.

require import GarbleTools.
  
require import ArrayExt.

import ForLoop.

require import SomeGarble.

import GSch.Sch.
import W.
import SomeGarble.DKCSecurity.WD.
import SomeGarble.DKCSecurity.D.
import SomeGarble.Tweak.


(***************)
(* Game Hybrid *)
(***************)

module GarbleHybridInit = {

  proc garb(yy : word, alpha : bool, bet : bool) : unit = {
    var twe, aa, bb : word;
        
    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ bet);
    aa = oget R.xx.[(G.a, C.v.[G.a] ^^ alpha)];
    bb = oget R.xx.[(G.b, C.v.[G.b] ^^ bet)];
    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ bet)] = E twe aa bb yy;
  }

  proc garb'(rn : bool, alpha : bool, bet : bool) : word = {
    var yy : word;
        
    yy = $W.Dword.dword;
    yy = if rn then yy else oget R.xx.[(G.g, oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ bet)])];
    garb(yy, alpha, bet);
    return yy;
  }
    
  proc init(l : int) : unit = {
    var tok : word;

    G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
    G.pp = map0;
    G.randG = map0;
    G.a = 0;
    G.b = 0;

    G.g = C.n;
    while (G.g < C.n + C.q) {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];

      garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
        
      tok = garb'(G.a <= l, true,  false);
      tok = garb'(G.b <= l,  false, true);
      G.yy.[G.g] = garb'(G.a <= l,  true,  true);
      
      if (G.a <= l < G.b /\ C.gg.[(G.g, !C.v.[G.a], false)] = C.gg.[(G.g, !C.v.[G.a], true)]) {
        garb(G.yy.[G.g], true, false);
      }
        
      G.g = G.g + 1;
    }
  }
}.

module GameHybrid (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
  proc garble (l : int) : bool = {
    var query : GSch.EncSecurity.query_IND;
    var p : GSch.EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query = ADV.gen_query();
        
    if (GSch.EncSecurity.queryValid_IND query) {
      real = ${0,1};
      p = if real then snd query else fst query;
      CircuitInit.init(p);
      RandomInit.init(true);
      GarbleHybridInit.init(l);

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

(**********************************************************)
(* Lemmas concerning the GameHybrid_0 ~ GameReal equality *)
(**********************************************************)

require import SomeGarbleReal.

equiv RinitE:
  RandomInit.init ~ RandomInit.init:
    ={useVisible, glob C} /\
    (0 <= C.m <= C.n + C.q){1} /\
    (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
      ={glob R} /\
      (validRand C.f R.xx){1} /\
      (Array.size R.t = (C.n+C.q)){1}.
proof. by conseq (_: ={useVisible,glob C} ==> ={glob R}) RandomInitH; sim. qed.
  
lemma GameReal_GameHybrid0 (A <: GSch.EncSecurity.Adv_IND_t{Rand,R,GameReal,GameHybrid}): 
  islossless A.gen_query =>
  islossless A.get_challenge => 
  equiv [GameReal(A).garble ~ GameHybrid(A).garble : ={glob A} /\ l{2} = -1 ==> ={res}].
proof.
  move => AgenL AgetL.
  proc.
  seq 1 1 : (={glob A, query} /\ l{2} = -1).
    by call (_ : true).
  (if; first by progress); last by auto.
    wp.
    call (_ : true) => //.
    wp.
    inline GarbleRealInit.init GarbleHybridInit.init. 
    while (={p, real, glob A, query, C.n, C.m, C.q, C.aa, C.bb, C.gg, G.g, C.v} /\ ={R.t} /\
      GSch.EncSecurity.queryValid_IND query{1} /\
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      l{2} = -1 /\
      l0{2} = l{2} /\
      (forall k b, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,b)] = R.xx{2}.[(k,b)]) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).

      inline*; auto. progress; first 7 by cut : false by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.  

      cut ->: C.aa{2}.[G.g{2}] <= -1 <=> false by idtac=>/#. cut ->: C.bb{2}.[G.g{2}] <= -1 <=> false by idtac=>/#. simplify. rewrite ?getP ?xor_true ?xor_false. simplify. case (k = G.g{2}) => hc. simplify. case (a = !R.t{2}.[C.aa{2}.[G.g{2}]]) => ha. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. cut ->: a = R.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. rewrite H4. idtac=> /#. done.
    
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    wp; call RandomInitEquiv; call CircuitInitEquiv.
    auto; progress.    
      by move : H; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= => /#. 
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      apply fmapP; rewrite /(==) => x; elim x => k a b => /#. 
      simplify encode; congr; apply fun_ext; rewrite /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hc. rewrite H22; first by idtac => /#. smt. done.   
qed.    

(**************************************************************)
(* Lemmas concerning the GameHybrid_bound ~ GameFake equality *)
(**************************************************************)

require import SomeGarbleFake.

lemma GameFake_GameHybridBound (A <: GSch.EncSecurity.Adv_IND_t{Rand,R,GameReal,GameHybrid}): 
  islossless A.gen_query =>
  islossless A.get_challenge => 
equiv [GameFake(A).garble ~ GameHybrid(A).garble : ={glob A} /\ l{2} = bound-1 ==> ={res}].
proof.
  move => AgenL AgetL.
  proc.
  seq 1 1 : (={glob A, query} /\ l{2} = bound-1).
    by call (_ : true).
  (if; first by progress); last by auto.
    wp.
    call (_ : true) => //.
    wp.
    inline GarbleInitFake.init GarbleHybridInit.init. 
    while (={p, real, glob A, query, C.n, C.m, C.q, C.aa, C.bb, C.gg, G.g, C.v} /\ ={R.t} /\
      GSch.EncSecurity.queryValid_IND query{1} /\
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      l{2} = bound-1 /\
      l0{2} = l{2} /\
      (forall k b, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,b)] = R.xx{2}.[(k,b)]) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).

      inline*; auto; progress; first 7 by cut : false by idtac=>/#. 
      by idtac=>/#.
      by idtac=>/#.

      cut ->: C.aa{2}.[G.g{2}] <= SomeGarble.bound - 1 <=> true by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. cut ->: C.bb{2}.[G.g{2}] <= SomeGarble.bound - 1 <=> true by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. simplify. rewrite ?getP ?xor_true ?xor_false. simplify. case (k = G.g{2}) => hc. simplify. case (a = !R.t{2}.[C.aa{2}.[G.g{2}]]) => ha. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. congr. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. case (b = ! R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. cut ->: a = R.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. cut ->: a = R.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. rewrite H4. idtac=> /#. done.

    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    wp; call RandomInitEquiv; call CircuitInitEquiv.
    auto; progress.
      by move : H; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=; case realL => /#.  
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      apply fmapP; rewrite /(==) => x; elim x => k a b => /#. 
      simplify encode. congr. apply fun_ext. rewrite /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hc. rewrite H22; first by idtac => /#. smt. done. 
qed.

(*************************************************)
(* Lemmas concerning probabilities of GameHybrid *)
(*************************************************)

lemma GameHybrid0_Game_IND_pr (A <: GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>  
  Pr[GameHybrid(A).garble((-1)) @ &m :res] = Pr[GSch.EncSecurity.Game_IND(Rand,A).main()@ &m:res].
proof.
  move => AgenL AgetL.
  cut <-: Pr[Game(Garble1,A).main()@ &m :res] = Pr[GSch.EncSecurity.Game_IND(Rand,A).main()@ &m:res]
    by byequiv (eqDefs A).
  cut <-: Pr[GameReal(A).garble()@ &m:res] = Pr[Game(Garble1,A).main()@ &m :res]
    by byequiv (equivRealInd_aux A AgenL AgetL).      
  cut ->: Pr[GameHybrid(A).garble(-1) @ &m : res] = Pr[GameReal(A).garble() @ &m : res] <=>
    Pr[GameReal(A).garble() @ &m : res] = Pr[GameHybrid(A).garble(-1) @ &m : res] by idtac=>/#.
  by byequiv (GameReal_GameHybrid0 A AgenL AgetL). 
qed.

lemma GameHybridBound_independent (A <: GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,R',C}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>  
  Pr[GameHybrid(A).garble(bound - 1)@ &m:res] = 1%r / 2%r.
proof.
  move => AgenL AgetL.
  rewrite -(GameFake_independent A &m) //=.
  cut ->: Pr[GameHybrid(A).garble(bound - 1) @ &m : res] = Pr[GameFake(A).garble() @ &m : res] <=> Pr[GameFake(A).garble() @ &m : res] = Pr[GameHybrid(A).garble(bound - 1) @ &m : res] by idtac=>/#.
  by byequiv (GameFake_GameHybridBound A AgenL AgetL).
qed.

lemma GameHybridBound_pr (A <: GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,R',C}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>  
  2%r * Pr[GameHybrid(A).garble(bound - 1)@ &m:res] = 1%r.
proof. by move => AgenL AgetL; rewrite (GameHybridBound_independent A &m) //. qed.
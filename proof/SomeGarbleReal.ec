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

(**************)
(** Game Real *)
(**************)

(**
  GarbleInitReal module
*)
(** Initialises the garbling values of Game Real *)
module GarbleRealInit = {
    
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
      
  proc init() : unit = {
    var tok : word;

    G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
    G.pp = map0;
    G.randG = map0;
    G.a = 0;
    G.b = 0;

    G.g = C.n;
    while (G.g < C.n + C.q)
    {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
        
      garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
        
      tok = garb'(false,  true, false);
      tok = garb'(false, false,  true);
      G.yy.[G.g] = garb'(false,  true,  true);
        
      G.g = G.g + 1;
    }
  }
}.

module GameReal (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
  proc garble () : bool = {
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
      GarbleRealInit.init();
        
      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
          
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = $DBool.dbool;
    }

    return ret;
  }
}.

module type Scheme_t = {
  proc enc(p:fun_t*input_t) : funG_t*inputG_t*outputK_t { }
}.

module Game(S:Scheme_t, ADV:GSch.EncSecurity.Adv_IND_t) = {
  proc main() : bool = {
    var query,p,c,b,adv,ret;

    query = ADV.gen_query();
    if (GSch.EncSecurity.queryValid_IND query) {
      b = ${0,1};
      p = if b then snd query else fst query;
      c = S.enc(p);
      adv = ADV.get_challenge(c);
      ret = (b = adv);
    }
    else {
      ret = ${0,1};
    }
    return ret;
  }
}.

(* Gb from figure 7 *)
module Garble1 : Scheme_t = {
  proc enc(p:fun_t*input_t) : funG_t*inputG_t*outputK_t = {
    CircuitInit.init(p);
    RandomInit.init(false);
    return (funG C.f R.xx, encode (inputK C.f R.xx) C.x, outputK C.f R.xx);
  }
}.

(*****************************************************)
(* Lemmas concerning the PrivInd ~ GameReal equality *)
(*****************************************************)
  
lemma eqDefs (A<:GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}):
  equiv[Game(Garble1,A).main ~ GSch.EncSecurity.Game_IND(Rand,A).main:
  ={glob A} ==> ={res}].
proof.
  proc; inline Game(Garble1,A).main.
  swap{2} 1 1; seq 1 1: (={query, glob A}); first by call (_: true).
  case (GSch.EncSecurity.queryValid_IND query{1}); last by rcondf{1} 1=> //; rcondf{2} 2; auto; smt.
  rcondt{1} 1=> //; rcondt{2} 2; first by auto.
  inline*; wp; call (_: true); wp.
  while (useVisible{1}= false /\ i0{1} = i{2} /\
    (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst (if b{1} then snd query{1} else fst query{1})) /\
    C.n{1} = n{2} /\ C.m{1} = m{2} /\ C.q{1} = q{2} /\
    C.aa{1} = aa{2} /\ C.bb{1} = bb{2} /\ ={glob A, R.xx}).
      by auto. 
  wp; while{1} (true) ((C.n + C.q - i){1}); first by auto; smt.
  by auto; progress => /#. 
qed.
  
lemma equivRealInd_aux (A <: GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameReal(A).garble ~ Game(Garble1,A).main : ={glob A} ==> ={res} ].
proof.  
  move => AgenL AgetL.
  proc.
  seq 1 1 : (={query} /\ ={glob A}).
    by call (_ : true) => //; auto; smt.
  if; first by progress.
    wp; call (_ : true) => //; wp.
    inline Garble1.enc GarbleRealInit.init.
    while{1} (={glob A} /\ t_xor (C.n{1} + C.q{1}) R.t{1} R.t{2} C.v{1} /\
      0 <= C.q{2} /\
      C.n{2} <= G.g{1} /\
      C.f{2} = ((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2}) /\ valid_circuitP bound C.f{2} /\
      let (topo, gg) = funG C.f{2} R.xx{2} in
        ={glob C} /\
        (forall i v, 0 <= i < C.n + C.q => getlsb (oget R.xx.[(i, v)]) = v ^^ R.t.[i]){2} /\
        (forall g u, 0 <= g < (C.n + C.q){1} => R.xx.[(g, u)]{1} = R.xx.[(g, u)]{2}) /\
        (forall i, C.n <= i < C.n + C.q =>
          C.v{2}.[i] = oget C.gg.[(i, false ^^ C.v{2}.[C.aa{2}.[i]], false ^^ C.v{2}.[C.bb.[i]])]){2} /\
        topo = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
        G.g{1} <= C.n{1} + C.q{1} /\
        (forall i a b, !(G.g{1} <= i < C.n{1} + C.q{1}) => gg.[(i, a, b)] = G.pp{1}.[(i, a, b)]))
        ((C.n + C.q - G.g){1}).
          move => &m z.
          inline GarbleRealInit.garb' GarbleRealInit.garb.
          swap 13 -12.
          swap 26 -25.
          swap 39 -38.
          wp; simplify; do 3 ! rnd; skip.
          simplify funG funG fst snd t_xor. 
          (progress;first 2 by idtac=>/#);last 4 by smt.
            case (G.g{hr} = i)=> hi.
              rewrite hi !getP get_initGates; first idtac=>/#.
              cut -> /=: C.n{m} <= i < C.n{m} + C.q{m} by idtac=>/#.
              rewrite !xor_true !xor_false /=.
              cut hneq : forall (x:bool), ((! x) = x) = false by idtac=>/#.
              cut lem : forall u v, Some (enc R.xx{m} ((C.n{m}, C.m{m}, C.q{m}, C.aa{m}, C.bb{m}), C.gg{m}) i
              (u ^^ R.t{hr}.[C.aa{m}.[i]]) (v ^^ R.t{hr}.[C.bb{m}.[i]])) =
                Some (E (tweak i (R.t{hr}.[C.aa{m}.[i]]^^u) (R.t{hr}.[C.bb{m}.[i]]^^v))
                (oget R.xx{hr}.[(C.aa{m}.[i], u ^^ C.v{m}.[C.aa{m}.[i]])]) (oget R.xx{hr}.[(C.bb{m}.[i], v ^^ C.v{m}.[C.bb{m}.[i]])]) (oget R.xx{hr}.[(i, (oget C.gg{m}.[(i, u^^C.v{m}.[C.aa{m}.[i]], v^^C.v{m}.[C.bb{m}.[i]])]))])).
                move => u v.
                simplify enc fst snd.
                rewrite !H3;first 4 by elim H2 => /#.
                rewrite !H ;first 2 by elim H2 => /#. 
                rewrite !H4 ;first 3 by elim H2 => /#. 
                rewrite !(Bool.xorC false) !xor_false.
                cut xor_simpl : forall x y z, x ^^ (y ^^ z) ^^ y = x ^^ z
                  by (move => x y z;case x;case y;case z;do rewrite /= ?(xor_true, xor_false) //).
                rewrite !xor_simpl.
                by do 2 !congr; rewrite Bool.xorC; [rewrite (Bool.xorC u) | rewrite (Bool.xorC v)]; rewrite Bool.xorA.
            (case (a = R.t{hr}.[C.aa{m}.[i]])=> ha;[rewrite ? ha|cut -> : a = !R.t{hr}.[C.aa{m}.[i]] by idtac=>/#]);
            (case (b0 = R.t{hr}.[C.bb{m}.[i]])=> hb;[rewrite hb|cut -> : b0 = !R.t{hr}.[C.bb{m}.[i]] by idtac=>/#]);rewrite ?hneq /=.
              by (cut := lem false false;rewrite (H5 i) ?(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //; first by idtac=>/#) => /#. 
              by cut := lem false true; rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //; simplify; progress; (cut ->: R.t{hr}.[C.aa{m}.[i]] = ! R.t{hr}.[C.aa{m}.[i]] <=> false by idtac=>/#); simplify => /#.  
              by cut := lem true false;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //; simplify; progress; (cut ->: R.t{hr}.[C.bb{m}.[i]] = ! R.t{hr}.[C.bb{m}.[i]] <=> false by idtac=>/#); simplify => /#.  
              by cut := lem true true;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //.
              cut h : forall aa bb, ((G.g{hr}, R.t{hr}.[C.aa{m}.[G.g{hr}]] ^^ aa, R.t{hr}.[C.bb{m}.[G.g{hr}]] ^^ bb) = (i, a, b0)) = false by idtac=>/#.
            by rewrite !getP; simplify; (cut ->: i = G.g{hr} <=> false by idtac=>/#); simplify; apply H7 => /#. 
    wp.
    call RandomGenClassicVisibleE.
    call CircuitInitEquiv.
    wp; rnd; skip.
    simplify funG funG fst.
    move => &1 &2 [[eq_query]] eq_adv valid.
    simplify validInputsP valid_circuitP fst snd.
    progress.
      by case realL => /#.
      by move : H1; case realL => /#.
      by move : H1; case realL => /#.     
      by move : H1; case realL => /#.
      by move : H1; case realL => /#.     
      by move : H1; case realL => /#. 
      by move : H1; case realL => /#. 
      by move : H1; case realL => /#. 
      by move : H1; case realL => /#. 
      move : valid; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP /fst /snd;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : H1; case realL => /#.     
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by (rewrite get_initGates; first by idtac=>/#); rewrite H21 map0P //=.  
      by idtac=>/#.
      apply fmapP=> y; elim y=> i a b =>/#. 
    by auto.
qed. 
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
import SomeGarble.DKCSecurity.
import SomeGarble.Tweak.

(*************)
(* Game Fake *)
(*************)
  
module GarbleInitFake = {

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
    while (G.g < C.n + C.q) {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];

      garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
        
      tok = garb'(true, true,  false);
      tok = garb'(true,  false, true);
      G.yy.[G.g] = garb'(true,  true,  true);
      
      G.g = G.g + 1;
    }
  }
}.

module GameFake (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
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
      GarbleInitFake.init();

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

lemma GarbleInitFakeL : islossless GarbleInitFake.init.
proof.
  proc.
  while true (C.n + C.q - G.g).
    progress; inline*; auto; simplify; smt.
  by auto => /#. 
qed.

(**********************************************)
(* ALTERNATIVE VERSION - easy-independent one *)
(**********************************************)

module R' = {
  var t : bool array
  var vv : (int,word) fmap
  var ii : (int,word) fmap
}.

module RandomInit' = {
  proc init(useVisible:bool): unit = {
    var i, tok1, tok2, v, trnd;

    R'.t = offun (fun x, false) (C.n + C.q);
    R'.vv = map0;
    R'.ii = map0;

    i = 0;
    while (i < C.n + C.q) {
      trnd = ${0,1};
      v = if useVisible then C.v.[i] else false;
      trnd = if (i < C.n + C.q - C.m) then trnd else v;
      tok1 = $W.Dword.dwordLsb ( trnd);
      tok2 = $W.Dword.dwordLsb (!trnd);

      R'.t.[i] = trnd;

      R'.vv.[i] = tok1;
      R'.ii.[i] = tok2;

      i = i + 1;
    }
  } 
}.

equiv Random'InitEquiv: RandomInit'.init ~ RandomInit'.init:
  ={useVisible, C.n, C.m, C.q, C.aa, C.bb} /\
  (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
    C.v{1}.[i] = C.v{2}.[i]) /\
    (0 <= C.m <= C.n + C.q){1} /\
    useVisible{1} /\
    (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
    ={R'.t} /\
    (forall g, 0 <= g < (C.n + C.q){1} => R'.vv.[g]{1} = R'.vv.[g]{2}) /\
    (forall g, 0 <= g < (C.n + C.q){1} => R'.ii.[g]{1} = R'.ii.[g]{2}) /\
    (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{1}) = !getlsb (oget R'.ii.[g]{1})) /\
    (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{2}) = !getlsb (oget R'.ii.[g]{2})) /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){1} /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){2}.
proof.
  proc => //.
  while (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i} /\
    (forall (i0 : int),
      C.n{1} + C.q{1} - C.m{1} <= i0 < C.n{1} + C.q{1} =>
      C.v{1}.[i0] = C.v{2}.[i0]) /\
    0 <= C.m{1} <= C.n{1} + C.q{1} /\
    useVisible{1} /\
    fst C.f{1} = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
    0 <= i{1} <= C.n{1} + C.q{1} /\
    (forall (g : int), 0 <= g < i{1} => R'.vv{1}.[g] = R'.vv{2}.[g]) /\
    (forall (g : int), 0 <= g < i{1} => R'.ii{1}.[g] = R'.ii{2}.[g]) /\
    (forall (g : int), 0 <= g < i{1} => R'.t{1}.[g] = R'.t{2}.[g]) /\
    (forall (g : int), 0 <= g < i{1} => getlsb (oget R'.vv{1}.[g]) = !getlsb (oget R'.ii{1}.[g])) /\
    (forall (g : int), 0 <= g < i{1} => getlsb (oget R'.vv{2}.[g]) = !getlsb (oget R'.ii{2}.[g])) /\
    (0 <= C.m{1} <= C.n{1} + C.q{1} /\ size R'.t{1} = C.n{1} + C.q{1}) /\
    (0 <= C.m{2} <= C.n{2} + C.q{2} /\ size R'.t{2} = C.n{2} + C.q{2})).
      auto; progress; first 6 by idtac=>/#.
        rewrite ?getP => /#.
        rewrite ?getP => /#.
        rewrite ?get_set => /#.
        rewrite ?getP; case (g = i{2}) => hc; smt.
        rewrite ?getP; case (g = i{2}) => hc; smt.
        by rewrite size_set.
        by rewrite size_set.
    auto; progress; first 3 by idtac=>/#.
      by rewrite size_offun max_ler => /#.
      by rewrite size_offun max_ler => /#.
      by rewrite arrayP => /#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
  qed.  

module GarbleInitFake' = {
    
  proc init() : unit = {
    var tok : word;
    var wa, wb : word;
    var twe : word;
      
    G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
    G.pp = map0;
    G.randG = map0;
    G.a = 0;
    G.b = 0;

    G.g = C.n;
    while (G.g < C.n + C.q) {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
        
      wa = oget R'.vv.[G.a];
      wb = oget R'.vv.[G.b];
      tok = oget R'.vv.[G.g];
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

      wa = oget R'.ii.[G.a];
      wb = oget R'.vv.[G.b];
      tok = $W.Dword.dword;
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
        
      wa = oget R'.vv.[G.a];
      wb = oget R'.ii.[G.b];
      tok = $W.Dword.dword;
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

      wa = oget R'.ii.[G.a];
      wb = oget R'.ii.[G.b];
      tok = $W.Dword.dword;
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

      G.yy.[G.g] = tok;

      G.g = G.g + 1;
    }
  }
}.
  
equiv GarbleInitFake'InitEquiv: GarbleInitFake'.init ~ GarbleInitFake'.init:
  ={C.n, C.m, C.q, C.aa, C.bb} /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => R'.vv{1}.[k] = R'.vv{2}.[k]) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = getlsb (oget R'.vv{2}.[k])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => R'.ii{1}.[k] = R'.ii{2}.[k]) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.ii{1}.[k]) = getlsb (oget R'.ii{2}.[k])) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = !getlsb (oget R'.ii{1}.[k])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{2}.[k]) = !getlsb (oget R'.ii{2}.[k])) /\
  (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
    (forall g a b, C.n{1} <= g < (C.n + C.q){1} => G.pp.[(g,a,b)]{1} = G.pp.[(g,a,b)]{2}) /\
    (forall g a b, !(C.n{1} <= g < (C.n + C.q){1}) => G.pp.[(g,a,b)]{1} = None) /\
    (forall g a b, !(C.n{1} <= g < (C.n + C.q){1}) => G.pp.[(g,a,b)]{2} = None).
proof.
  proc => //.
  while (={C.n, C.m, C.q, C.aa, C.bb} /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => R'.vv{1}.[k] = R'.vv{2}.[k]) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => R'.ii{1}.[k] = R'.ii{2}.[k]) /\
    validInputsP (C.f{1}, C.x{1}) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = !getlsb (oget R'.ii{1}.[k])) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{2}.[k]) = !getlsb (oget R'.ii{2}.[k])) /\
    (forall (k : int), 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = getlsb (oget R'.vv{2}.[k])) /\
    (forall (k : int), 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.ii{1}.[k]) = getlsb (oget R'.ii{2}.[k])) /\
    fst C.f{1} = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
    (forall (g : int) (a b : bool), C.n{1} <= g < G.g{1} => G.pp{1}.[(g, a, b)] = G.pp{2}.[(g, a, b)]) /\
    (forall g a b, C.n{1} <= g < G.g{1} => mem (dom G.pp{1}) (g,a,b)) /\
    (forall g a b, C.n{1} <= g < G.g{1} => mem (dom G.pp{2}) (g,a,b)) /\
    (forall g a b, g < C.n{1} => !mem (dom G.pp{1}) (g,a,b)) /\
    (forall g a b, G.g{1} <= g => !mem (dom G.pp{1}) (g,a,b)) /\
    (forall g a b, g < C.n{1} => !mem (dom G.pp{2}) (g,a,b)) /\
    (forall g a b, G.g{1} <= g => !mem (dom G.pp{2}) (g,a,b)) /\
    (forall g a b, g < C.n{1} => G.pp{1}.[(g, a, b)] = None) /\
    (forall g a b, G.g{1} <= g => G.pp{1}.[(g, a, b)] = None) /\
    (forall g a b, g < C.n{1} => G.pp{2}.[(g, a, b)] = None) /\
    (forall g a b, G.g{1} <= g => G.pp{2}.[(g, a, b)] = None) /\
    ={G.g} /\ C.n{1} <= G.g{1} <= C.n{1} + C.q{1}).
      auto; progress.
        rewrite ?getP //=. case (g = G.g{2}) => hc. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. simplify => /#. simplify. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. simplify =>/#. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify => /#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify => /#. simplify => /#. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. smt.

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.
    
        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        by idtac=>/#.
        by idtac=>/#. 

    wp; skip; progress; first 2 by idtac=>/#. 
      by rewrite dom0 in_fset0.  
      by rewrite dom0 in_fset0.  
      by rewrite dom0 in_fset0.   
      by rewrite dom0 in_fset0.  
      by rewrite map0P. 
      by rewrite map0P. 
      by rewrite map0P. 
      by rewrite map0P. 
      by idtac=>/#. 
      by idtac=>/#. 
      by idtac=>/#. 
      by idtac=>/#. 
  qed.
  
module GameFake' (ADV:GSch.EncSecurity.Adv_IND_t) = {
  
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
      RandomInit'.init(true);
      GarbleInitFake'.init();

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), offun (fun g, oget (filter (fun a b, 0 <= a < C.n) R'.vv).[g]) C.n, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

equiv RandomInit_RandomInit' : RandomInit.init ~ RandomInit'.init:
  ={useVisible, C.n, C.m, C.q, C.aa, C.bb} /\
  (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
    C.v{1}.[i] = C.v{2}.[i]) /\
  (0 <= C.m <= C.n + C.q){1} /\
  useVisible{1} /\
  (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
    R.t{1} = R'.t{2} /\
    (forall g, 0 <= g < (C.n + C.q){1} => R.xx{1}.[(g, C.v{1}.[g])] = R'.vv{2}.[g]) /\
    (forall g, 0 <= g < (C.n + C.q){1} => R.xx{1}.[(g, !C.v{1}.[g])] = R'.ii{2}.[g]) /\
    (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = getlsb (oget R'.vv{2}.[k])) /\
    (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = !getlsb (oget R'.ii{2}.[k])) /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R.t = (C.n+C.q)){1} /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){2}.
proof.
  proc => //.
  seq 3 4 : (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i} /\
    (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
      C.v{1}.[i] = C.v{2}.[i]) /\
    (0 <= C.m <= C.n + C.q){1} /\
    useVisible{1} /\
    (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} /\ R.t{1} = R'.t{2} /\
    R.t{1} = offun (fun (_ : int) => false) (C.n + C.q){2} /\
    size R.t{1} = (C.n + C.q){2} /\ R.xx{1} = map0 /\
    R'.vv{2} = map0 /\ R'.ii{2} = map0 /\ i{1} = 0).
      by auto; progress; expect 1 by rewrite size_offun max_ler => /#. 
  while (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i} /\
    (forall (i0 : int),
      C.n{1} + C.q{1} - C.m{1} <= i0 < C.n{1} + C.q{1} =>
      C.v{1}.[i0] = C.v{2}.[i0]) /\
    0 <= C.m{1} <= C.n{1} + C.q{1} /\
    useVisible{1} /\
    fst C.f{1} = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
    R.t{1} = R'.t{2} /\
    size R.t{1} = C.n{2} + C.q{2} /\ size R'.t{2} = C.n{2} + C.q{2} /\
    (forall g, 0 <= g < i{1} => R.xx{1}.[(g, C.v{1}.[g])] = R'.vv{2}.[g]) /\
    (forall g, 0 <= g < i{1} => R.xx{1}.[(g, !C.v{1}.[g])] = R'.ii{2}.[g]) /\
    (forall k, 0 <= k < i{1} => R.t{1}.[k] = getlsb (oget R'.vv{2}.[k])) /\
    (forall k, 0 <= k < i{1} => R.t{1}.[k] = !getlsb (oget R'.ii{2}.[k]))).
      auto; progress; first 5 by idtac=>/#.
        by rewrite size_set.
        by rewrite size_set.
        rewrite ?getP H2 //= /#. 
        rewrite ?getP H2 //= /#. 
        rewrite ?getP ?get_set; first by idtac=>/#. rewrite H2 //=. case (i{2} < C.n{2} + C.q{2} - C.m{2}) => hi. case (k = i{2}) => hk. rewrite oget_some; first by smt. idtac=>/#. case (k = i{2}) => hk; first by smt. idtac=>/#.
        rewrite ?getP ?get_set; first by idtac=>/#. rewrite H2 //=. case (i{2} < C.n{2} + C.q{2} - C.m{2}) => hi. case (k = i{2}) => hk. rewrite oget_some; first by smt. idtac=>/#. case (k = i{2}) => hk; first by smt. idtac=>/#.
  by auto; progress => /#. 
qed.

lemma same_fakes (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}):
  equiv[GameFake(A).garble ~ GameFake'(A).garble : ={glob A} ==> ={res}].
proof.
  proc => //.
  seq 1 1 : (={glob A, query}).
    by call (_ : true).
  if; first by progress.
    wp; call (_ : true); wp.
    inline GarbleInitFake.init GarbleInitFake'.init.
    while (={p, real, glob A, query, C.n, C.m, C.q, C.aa, C.bb, C.gg, G.g, C.v} /\ R.t{1} = R'.t{2} /\
      GSch.EncSecurity.queryValid_IND query{1} /\
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,C.v{1}.[k])] = R'.vv{2}.[k]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,!C.v{1}.[k])] = R'.ii{2}.[k]) /\
      (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = getlsb (oget R'.vv{2}.[k])) /\
      (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = !getlsb (oget R'.ii{2}.[k])) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).
      inline*; auto; progress; first 2 by idtac=>/#.

        rewrite ?getP ?xor_false ?xor_true //=.
        case (k = G.g{2}) => hk. case (a = ! R'.t{2}.[C.aa{2}.[G.g{2}]]) => ha. case (b = ! R'.t{2}.[C.bb{2}.[G.g{2}]]) => hb.
        cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] <=> false by idtac=>/#.
        cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] <=> false by idtac=>/#.

        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> true. simplify. rewrite ha. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. 
        cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true. simplify. rewrite hb. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done.

        simplify. 

        congr. congr. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H4. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. rewrite H4. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done.

        simplify. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify.  
        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. rewrite ha. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = ! getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. 

        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true. simplify. rewrite ha. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. rewrite -H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.
        cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. simplify. rewrite ha. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.

        simplify.

        congr. congr. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#.  done. cut ->: R'.t{2}.[C.bb{2}.[G.g{2}]] = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H4; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H3; first rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.

        simplify.

        case (b = ! R'.t{2}.[C.bb{2}.[G.g{2}]]) => hb. simplify. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. 

        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. simplify. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. rewrite hb. rewrite H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. by cut ->: (! getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. 
        cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true. simplify. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. rewrite hb. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. by rewrite -H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. 

        simplify.

        congr. congr. rewrite H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = ! getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite -H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#.  done. congr. rewrite H3; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H4; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.

        simplify.

        cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] && b = R'.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. 
        cut->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H6; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.
        
        cut->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H6; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.
 
        cut->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> false. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H6; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.

        cut->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H5; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. 

         simplify.

         congr. congr. rewrite H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. rewrite H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. rewrite H3; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H3; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.

        rewrite ?getP ?xor_false ?xor_true //= /#.
        simplify; rewrite ?getP ?xor_false ?xor_true //= /#.
        rewrite ?getP ?xor_false ?xor_true //= /#. 
        rewrite ?getP ?xor_false ?xor_true //= /#.    
        rewrite ?getP ?xor_false ?xor_true //= /#.   
        rewrite ?getP ?xor_false ?xor_true //= /#.     

      wp; call RandomInit_RandomInit'; call CircuitInitEquiv.
      auto; progress. 
        by case realL => hr; move : H; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput; simplify validInputsP. 
        by idtac=>/#.              
        by idtac=>/#.
        by idtac=>/#.        
        by rewrite map0P.        
        by rewrite map0P.
        by rewrite map0P.
        by rewrite map0P.
        rewrite fmapP => x; elim x => k a b => /#.
        simplify encode. congr. rewrite fun_ext /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hx. case (mem (dom xx_L) (x, x_R.[x])) => hxx. cut ? : xx_L.[(x, x_R.[x])] <> None by rewrite -in_dom. cut ? : vv_R.[(x)] <> None by rewrite -H26 => /#. cut ->: mem (dom vv_R) x <=> true by rewrite in_dom. simplify. idtac=>/#. cut ? : xx_L.[(x, x_R.[x])] = None by smt. cut ? : vv_R.[(x)] = None by rewrite -H26 => /#. cut ->: mem (dom vv_R) x <=> false by smt. by simplify. by simplify.
        by idtac=>/#.
    by auto.
qed.

module GameFake'' (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
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
      p = fst query;
      CircuitInit.init(p);
      RandomInit'.init(true);
      GarbleInitFake'.init();

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), offun (fun g, oget (filter (fun a b, 0 <= a < C.n) R'.vv).[g]) C.n, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

lemma GameFake'_GameFake'' (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}) &m :
  equiv[GameFake'(A).garble ~ GameFake''(A).garble : ={glob A} ==> ={res}].
proof.
  proc.
  seq 1 1 : (={glob A, query}).
    call (_ : true) => //.
  if; first by progress.
    wp; call (_ : true); wp.
    seq 4 4 : (
      (={glob A, query, real, C.n, C.m, C.q, C.aa, C.bb} /\
      (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i]) /\
      (eval C.f C.x){1} = (eval C.f C.x){2} /\
      (((C.n, C.m, C.q, C.aa, C.bb), C.gg) = C.f /\
        Array.size C.v = (C.n + C.q) /\
        validInputsP (C.f, C.x)){1} /\
      (forall i, 0 <= i < C.n{1} => C.v{1}.[i] = C.x{1}.[i]) /\
      (((C.n, C.m, C.q, C.aa, C.bb), C.gg) = C.f /\
        Array.size C.v = (C.n + C.q) /\
        validInputsP (C.f, C.x)){2} /\
      (forall i, 0 <= i < C.n{1} => C.v{2}.[i] = C.x{2}.[i])) /\
      ={R'.t} /\
      (forall g, 0 <= g < (C.n + C.q){1} => R'.vv.[g]{1} = R'.vv.[g]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => R'.ii.[g]{1} = R'.ii.[g]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{1}) = !getlsb (oget R'.ii.[g]{1})) /\
      (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{2}) = !getlsb (oget R'.ii.[g]{2})) /\
      (0 <= C.m <= C.n + C.q /\
        Array.size R'.t = (C.n+C.q)){1}).    

        call Random'InitEquiv.
        call InitEquiv_rnd.
        auto; progress; first 4 by idtac=>/#.
          by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
          by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
    call GarbleInitFake'InitEquiv.
    auto; progress; first 2 by idtac=>/#. 
      by apply fmapP; rewrite /(==) => x; elim x => g a b => /#. 
      congr. apply fun_ext; rewrite /(==) => x. congr. rewrite ?filterP. simplify. case (0 <= x < C.n{2}) => hc; last by done. simplify. cut ? : C.n{2} < C.n{2} + C.q{2}. move : H2. simplify validInputsP valid_circuitP fst snd => /#. rewrite ?H7. idtac => /#. congr. smt. 
    by auto.
qed.

lemma GameFake''_independent (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}) &m :
  islossless A.gen_query =>
  islossless A.get_challenge =>
  Pr[GameFake''(A).garble() @ &m: res] = 1%r / 2%r.
proof.
  move => AgenLL AgetLL.
  byphoare => //; proc.
  seq 1 : true (1%r) (1%r/2%r) (0%r) _ true => //; first by call (_ : true).
  if; last by rnd; skip; smt. 
    wp.
    swap 1 6.
    rnd ((=) adv).
    conseq (_ : true) =>//; first by progress;case adv0;smt. 
    call (_ : true) => //.
    wp. 
    inline GarbleInitFake'.init.
    while (true) (C.n + C.q - G.g).
      auto; progress; expect 2 by smt.
    auto. 
    inline RandomInit'.init.
    while true (C.n + C.q - i).
      auto; progress; expect 4 by smt.  
    auto.
    inline CircuitInit.init.
    while true (C.n + C.q - i0).
      auto; progress; expect 1 by idtac=>/#.
    auto; progress => /#.
qed.


lemma GameFake_independent (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}) &m :
  islossless A.gen_query =>
  islossless A.get_challenge =>
  Pr[GameFake(A).garble() @ &m: res] = 1%r / 2%r.
proof.
  move => AgenL AgetL.
  rewrite -(GameFake''_independent A &m AgenL AgetL).
  cut <-: Pr[GameFake'(A).garble() @ &m : res] = Pr[GameFake''(A).garble() @ &m : res] by
    byequiv (GameFake'_GameFake'' A &m).
  by byequiv (same_fakes A).
qed.

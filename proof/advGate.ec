require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.
require import Array.

require import Dkc.
require import Gate.
require import GarbleTools.


  module A:Gate.Adv = {
    fun gen_query() : query = { var x : query; return x;}
    fun get_challenge(answer:answer) : bool = { var x : bool; return x;}
  }.

module Adv(Adv:Gate.Adv) : Dkc.Adv = {
  var c : bool
  var fc : Gate.funct
  var xc : Gate.input
  var tau : bool

  var input : Gate.inputG
  var g : ((bool*bool), token) map

  var l : int

  var t : bool

  fun gen_queries0() : Dkc.query list = {

    t = $Dbool.dbool;

    return [
      ((0,  t), (1, Gate.eval fc (!(fst xc), false)), true, tweak 0 tau   t ) ;
      ((0, !t), (1, Gate.eval fc (!(fst xc),  true)), true, tweak 0 tau (!t))
      ];
  }

  fun compute0(answers:Dkc.answer list) : unit = {
    var x : tokens;
    var key : token;
    var inp : token*token;
    var out : token*token;
    var ki0, ko0, r0 : token*token*token = hd answers;
    var ki1, ko1, r1 : token*token*token = hd (tl answers);

    if (Gate.eval fc (!(fst xc), false) = Gate.eval fc (!(fst xc), true))
    {
      key = $Dkc.genRandKeyLast(!(Gate.eval fc (!(fst xc), false)));
      if (Gate.eval fc (!(fst xc), false))
        out = (key, ko0);
      else
        out = (ko0, key);
    }
    else
    {
      if (Gate.eval fc (!(fst xc), false))
        out = (ko1, ko0);
      else
        out = (ko0, ko1);
    }
    
    key = $Dkc.genRandKeyLast(!tau);

    if (tau)
      inp = (Bitstring.zeros 0, key);
    else
      inp = (key, Bitstring.zeros 0);

    x = Array.empty:::(ki0, ki1):::inp:::out;

    input = Gate.encrypt x xc;

    g = Map.empty;
    g.[(!tau, false)] = enc x fc 0 1 2 (!tau) false;
    g.[(!tau,  true)] = enc x fc 0 1 2 (!tau)  true;
    g.[( tau,    t)] = r0;
    g.[( tau,   !t)] = r1;
  }
  
  fun gen_queries1() : Dkc.query list = {

    t = $Dbool.dbool;

    return [((0, t^^(fst xc)), (1, Gate.eval fc (fst xc, !(snd xc))), false, tweak 0 (t^^(fst xc)) tau)];
  }
  

  fun compute1(answers:Dkc.answer list) : unit =  {
    var x : tokens;
    var key : token;
    var key2 : token;
    var key3 : token;
    var k0 : token*token;
    var k1 : token*token;
    var k2 : token*token;
    var ki, ko, r : token*token*token = hd answers;

    key = $Dkc.genRandKeyLast(!t);
    if (fst xc)
      k0 = (key ,ki);
    else
      k0 = (ki, key);

    key2 = $Dkc.genRandKeyLast(!tau);

    if (tau)
      k1 = (Bitstring.zeros 0, key2);
    else
      k1 = (key2, Bitstring.zeros 0);

    key3 = $Dkc.genRandKeyLast(!(Gate.eval fc (fst xc, !(snd xc))));

    if (Gate.eval fc (fst xc, !(snd xc)))
      k2 = (key3, ko);
    else
      k2 = (ko, key3);

    x = Array.empty:::k0:::k1:::k2;
    
    input = Gate.encrypt x xc;
    
    g.[(  t^^(fst xc), !tau)] = enc x fc 0 1 2 (t^^(fst xc)) (!tau);
    g.[(  t^^(fst xc),  tau)] = r;
    key = $Dkc.genRandKey;
    key2 = $Dkc.genRandKey;
    k2 = (key, key2);
    
    x = Array.empty:::k0:::k1:::k2;
    g.[( !t^^(fst xc), false)] = enc x fc 0 1 2 (!t^^(fst xc)) false;
    g.[( !t^^(fst xc),  true)] = enc x fc 0 1 2 (!t^^(fst xc)) true;
  }
  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 1;
  }

  fun gen_queries(info:bool) : Dkc.query list = {
    var query : Gate.query;
    var ret : Dkc.query list;
    c = $Dbool.dbool;
    query := A.gen_query();
    tau = info;
    if (c) (fc, xc) = fst query; else (fc, xc) = snd query;
    if (l=0) ret := gen_queries0();
    if (l=1) ret := gen_queries1();
    return ret;
  }
  
  fun get_challenge(answers:Dkc.answer list) : bool = {
    var challenge : bool;
    var gg : Gate.functG;
    if (l=0) compute0(answers);
    if (l=1) compute1(answers);
    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge := A.get_challenge((gg, input, tt));
    return c = challenge;
  }

  fun fake() : bool = {
    var c : bool;
    var query : Gate.query;
    var ret : Dkc.query list;
    var challenge : bool;
    var gg : Gate.functG;
    var x : random;
    var v : bool;
    var t0 : bool;
    var t1 : bool;
    var k0 : token*token;
    var k1 : token*token;
    var f0 : Gate.funct;
    var x0 : Gate.input;
    var f1 : Gate.funct;
    var x1 : Gate.input;
    var key : token;
    var key1 : token;

    query := A.gen_query();
    (f0, x0) = fst query;
    (f1, x1) = snd query;
    v = Gate.eval f0 x0;
    
    t0 = $Dbool.dbool;
    t1 = $Dbool.dbool;

    key = $Dkc.genRandKeyLast(t0);
    key1 = $Dkc.genRandKeyLast(!t0);
    if (t0)
      k0 = (key1, key);
    else
      k0 = (key, key1);

    key = $Dkc.genRandKeyLast(t1);
    key1 = $Dkc.genRandKeyLast(!t1);
    if (t1)
      k1 = (key1, key);
    else
      k1 = (key, key1);

    keyFromDkc = $Dkc.genRandKey;
    x = Array.empty:::k0:::k1:::(key, key);
    g.[(  t0, !t1)] =  enc x fc 0 1 2   t0  (!t1);
    key = $Dkc.genRandKeyLast(Gate.eval f1 x1);
    x = Array.empty:::k0:::k1:::(key, key);
    g.[(  t0,  t1)] =  enc x fc 0 1 2   t0    t1 ;
    key = $Dkc.genRandKey;
    x = Array.empty:::k0:::k1:::(key, key);
    g.[( !t0,  t1)] =  enc x fc 0 1 2 (!t0)   t1 ;
    key = $Dkc.genRandKey;
    x = Array.empty:::k0:::k1:::(key, key);
    g.[( !t0, !t1)] =  enc x fc 0 1 2 (!t0) (!t1);

    input = Gate.encrypt x xc;

    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge := A.get_challenge((gg, input, tt));
    c = $Dbool.dbool;
    return c = challenge;
  }

}.

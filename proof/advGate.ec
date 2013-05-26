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
    var keynt : token;
    var keyntau : token;
    var keyCorrect : token;
    var key_nt_ntau : token;
    var key_nt_tau : token;
    var nko : token;
    var ki, ko, r : token*token*token = hd answers;
    var v : bool;
    v = Gate.eval fc (fst xc, !(snd xc));

    if (v = Gate.eval fc xc)
      keyCorrect = ko;
    else
      keyCorrect = $Dkc.genRandKeyLast(!(Gate.eval fc (fst xc, !(snd xc))));

    keynt = $Dkc.genRandKeyLast(!t^^(fst xc));
    keyntau = $Dkc.genRandKeyLast(!tau);

    key_nt_tau = $Dkc.genRandKey;
    key_nt_ntau = $Dkc.genRandKey;(*May be the same*)

    input = (ki, keyntau);
    g.[(  t^^(fst xc), !tau)] = Dkc.encode
      (tweak 2 (t^^(fst xc)) (!tau))
      ki
      keyntau
      keyCorrect;
    g.[(  t^^(fst xc),  tau)] = r;
    g.[( !t^^(fst xc), tau)] = Dkc.encode
      (tweak 2 (!t^^(fst xc)) (tau))
      keynt
      keyntau(*ETRANGE*)
      key_nt_ntau;
    g.[( !t^^(fst xc), tau)] = Dkc.encode
      (tweak 2 (!t^^(fst xc)) (tau))
      ki
      keyntau(*ETRANGE*)
      key_nt_tau;
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
    var v : bool;
    var t0 : bool;
    var t1 : bool;
    var f0 : Gate.funct;
    var x0 : Gate.input;
    var f1 : Gate.funct;
    var x1 : Gate.input;
    var keyFromDkc : token;
    var keyt1 : token;
    var keynt1 : token;
    var keyt0 : token;
    var keynt0 : token;
    var keyCorrect : token;
    var key_nto_t1 : token;
    var key_to_nt1 : token;
    var key_nto_nt1 : token;

    t1 = $Dbool.dbool;

    query := A.gen_query();
    (f0, x0) = fst query;
    (f1, x1) = snd query;
    v = Gate.eval f0 x0;
    
    t0 = $Dbool.dbool;

    keyt0 = $Dkc.genRandKeyLast(t0);
    keynt1 = $Dkc.genRandKeyLast(!t1);
    key_to_nt1  = $Dkc.genRandKey;
    keyCorrect = $Dkc.genRandKeyLast(v);

    keynt0 = $Dkc.genRandKeyLast(!t0);
    keyt1 = $Dkc.genRandKeyLast(t1);

    key_nto_t1  = $Dkc.genRandKey;
    key_nto_nt1 = $Dkc.genRandKey;

    input = (keyt0, keyt1);
    
    g.[( t0, t1)] = Dkc.encode
      (tweak 2 t0 t1)
      keyt0
      keyt1
      keyCorrect;
    g.[( !t0, t1)] = Dkc.encode
      (tweak 2 (!t0) t1)
      keynt0
      keyt1
      key_nto_t1;
    g.[( t0, !t1)] = Dkc.encode
      (tweak 2 t0 (!t1))
      keyt0
      keynt1
      key_to_nt1;
    g.[( !t0, !t1)] = Dkc.encode
      (tweak 2 (!t0) (!t1))
      keynt0
      keynt1
      key_nto_nt1;

    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge := A.get_challenge((gg, input, tt));
    c = $Dbool.dbool;
    return c = challenge;
  }

}.

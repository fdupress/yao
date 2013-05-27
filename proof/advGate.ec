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
  var good : bool

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
    var rand : bool;

    t = $Dbool.dbool;

    rand = $Dbool.dbool;

    return [
      ((0,  t^^(fst xc)), (1, Gate.eval fc (  fst xc , !(snd xc))), false, tweak 0 (!t^^(fst xc)) tau);
      ((0, !t^^(fst xc)), (2, rand), false, tweak 0 (!t^^(fst xc)) tau)
    ];
  }
  

  fun compute1(answers:Dkc.answer list) : unit =  {
    var keyt : token;
    var keynt : token;
    var keyntau : token;
    var key_t_tau : token;
    var key_nt_ntau : token;
    var key_nt_tau : token;
    var key_t_ntau : token;
    var r_t_tau : token;
    var r_nt_tau : token;

    (keyt, key_t_tau, r_t_tau) = hd answers;
    (keynt, key_nt_tau, r_nt_tau) = hd (tl answers);

    if (Gate.eval fc xc=Gate.eval fc (fst xc, !(snd xc)))
      key_t_ntau = key_t_tau;
    else
    {
      if (Gate.eval fc xc=Gate.eval fc (fst xc, !(snd xc)))
        key_t_ntau = key_nt_tau;
      else
        key_t_ntau = $Dkc.genRandKeyLast(Gate.eval fc xc);
    }
    
    keyntau = $Dkc.genRandKeyLast(!tau);

    key_nt_ntau = $Dkc.genRandKey;

    input = (keyt, keyntau);
    g.[(  t^^(fst xc), !tau)] = Dkc.encode
      (tweak 2 (t^^(fst xc)) (!tau))
      keyt
      keyntau
      key_t_ntau;
    g.[(  t^^(fst xc),  tau)] = r_t_tau;
    g.[( !t^^(fst xc), tau)] = r_nt_tau;
    g.[( !t^^(fst xc), !tau)] = Dkc.encode
      (tweak 2 (!t^^(fst xc)) (!tau))
      keynt
      keyntau
      key_nt_ntau;
  }
  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 1;
  }

  fun gen_queries(info:bool) : Dkc.query list = {
    var query : Gate.query;
    var query0 : Gate.funct*Gate.input;
    var query1 : Gate.funct*Gate.input;
    var ret : Dkc.query list;
    c = $Dbool.dbool;
    query := A.gen_query();
    query0 = fst query;
    query1 = snd query;
    tau = info;
    if (Gate.eval (fst query0) (snd query0) = Gate.eval (fst query0) (snd query0))
    {
      if (c) {
        fc = fst (fst query);
        xc = snd (fst query);
      } else {
        fc = fst (snd query);
        xc = snd (snd query);
      }
      if (l=0) ret := gen_queries0();
      if (l=1) ret := gen_queries1();
      good = false;
    }
    else
    {
      good = true;
      ret = [];
    }
    return ret;
  }
  
  fun get_challenge(answers:Dkc.answer list) : bool = {
    var challenge : bool;
    var gg : Gate.functG;
    if (good)
    {
      if (l=0) compute0(answers);
      if (l=1) compute1(answers);
      gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
      challenge := A.get_challenge((gg, input, tt));
    }
    else
      challenge = $Dbool.dbool;
    return c = challenge;
  }

}.

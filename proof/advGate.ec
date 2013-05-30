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

module Adv(A:Gate.Adv) : Dkc.Adv = {
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

  (* tau = !t^^(fst xc) *)
  (* !t^^(snd xc) = tau *)

    t = $Dbool.dbool;

    return [
      ((0,  t^^(snd xc)), (1, Gate.eval fc (!(fst xc),  (snd xc))), true, tweak 0 tau ( t^^(snd xc)));
      ((0, !t^^(snd xc)), (1, Gate.eval fc (!(fst xc), !(snd xc))), true, tweak 0 tau (!t^^(snd xc)))
      ];
  }

  fun compute0(answers:Dkc.answer list) : unit = {
    var x : tokens;
    var key : token;
    var inp : token*token;
    var out : token*token;
    var keyt : token;
    var keynt : token;
    var keyntau : token;
    var key_ntau_nt : token;
    var key_ntau_t : token;
    var key_tau_nt : token;
    var key_tau_t : token;
    var r_tau_t : token;
    var r_tau_nt : token;
    var outTok : (bool, token) map;

    ( keyt,  key_tau_t,  r_tau_t) = hd answers;
    (keynt, key_tau_nt, r_tau_nt) = hd (tl answers);

    outTok.[Gate.eval fc (!(fst xc), (snd xc))] = key_tau_t;
    if (Gate.eval fc (!(fst xc), (snd xc)) = Gate.eval fc (!(fst xc), !(snd xc)))
      outTok.[Gate.eval fc (!(fst xc), !(snd xc))] = $Dkc.genRandKeyLast(Gate.eval fc (!(fst xc), !(snd xc)));
    else
      outTok.[Gate.eval fc (!(fst xc), !(snd xc))] = key_tau_nt;

    outTok.[Gate.eval fc ((fst xc), !(snd xc))] = key_ntau_nt;
    outTok.[Gate.eval fc ((fst xc),  (snd xc))] = key_ntau_t;

    keyntau = $Dkc.genRandKeyLast(!tau);

    input = (keyntau, keyt);

    g = Map.empty;
    g.[(!tau, !t^^(snd xc))] = Dkc.encode (tweak 2 (!tau) (!t^^(snd xc))) keyntau keynt key_ntau_nt;
    g.[(!tau,  t^^(snd xc))] = Dkc.encode (tweak 2 (!tau) ( t^^(snd xc))) keyntau keyt  key_ntau_t;
    g.[( tau,  t^^(snd xc))] = r_tau_t;
    g.[( tau, !t^^(snd xc))] = r_tau_nt;
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
      key_t_ntau = $Dkc.genRandKeyLast(Gate.eval fc xc);
    
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
    if (c) {
      fc = fst (fst query);
      xc = snd (fst query);
    } else {
      fc = fst (snd query);
      xc = snd (snd query);
    }
    query0 = fst query;
    query1 = snd query;
    if (Gate.queryValid query)
    {
      tau = info;
      if (l=0) ret := gen_queries0();
      if (l=1) ret := gen_queries1();
      good = true;
    }
    else
    {
      good = false;
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

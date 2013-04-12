require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.

require import Dkc.
require import Gate.

cnst unit : unit.

op get(x:'a*'a, i:int) : 'a = let (a, b) = x in if i = 1 then a else b.
op set(x:'a*'a, i:int, v:'a) : 'a*'a = let (a, b) = x in if i = 1 then (v, b) else (a, v).

module Adv(Adv:Gate.Scheme.Adv) : Dkc.Adv = {
  var fc : Gate.funct
  var xc : Gate.input
  var tau : bool
  var l : int

  var input : Gate.inputG
  var g : ((bool*bool), token) map.
  var preG : ((bool*bool), Gate.token) map
  var x : (int*bool, Gate.token) map
  var t : (int, bool) map

  fun common0() : unit = {
    x = Map.empty;
    preG = Map.empty;
    g = Map.empty;
    t = Map.empty;
    t.[1] = $Dbool.dbool;
    t.[2] = $Dbool.dbool;
    t.[3] = false;
  }

  fun initX(i:int, b:bool) : unit = {
    x.[(i, b)] = $Dkc.genRandKeyLast((proj t.[1])^^b);
  }
  fun common1() : unit = {
    initX(1, false);
    initX(1,  true);
    initX(2, false);
    initX(2,  true);
    initX(3, false);
    initX(3,  true);
  }

  fun initPreG(a:bool, b:bool) : unit = {
    preG.[(a, b)] = proj x.[(3, Gate.eval fc (a, b))];
  }
  fun common2() : unit = {
    initPreG(false, false);
    initPreG( true, false);
    initPreG(false,  true);
    initPreG( true,  true);
  }
  
  fun initG(a:bool, b:bool) : unit = {
    g.[(a, b)] = Dkc.encode (Gate.tweak a b) (proj x.[(1, a)]) (proj x.[(2, b)]) (proj x.[(3, Gate.eval fc (a, b))]);
  }
  fun initInput(i:int) : unit = {
    input = set input i (proj x.[(i, (get xc i))]);
  }
  fun common3() : unit = {
    initG(false, false);
    initG(false,  true);
    initG( true, false);
    initG( true,  true);
    initInput(1);
    initInput(2);
  }

  fun gen_queries1() : Dkc.query list = {
    var x1 : bool = get xc 1;
    var t1 : bool = ! x1 ^^ tau;
    var val0 : bool = Gate.eval fc (x1, false);
    var val1 : bool = Gate.eval fc (x1, true);
    
    common0();
    
    t.[1] = t1;

    common1();

    return [((1,  t1), (2, val0), true, Gate.tweak   t1  tau) ; ((1, !t1), (2, val1), true, Gate.tweak (!t1) tau)];
  }

  fun computeG1(answers:Dkc.answer list) : unit = {
    var x1 : bool = get xc 1;
    var t1 : bool = ! x1 ^^ tau;
    var val0 : bool = Gate.eval fc (x1, false);
    var val1 : bool = Gate.eval fc (x1, true);

    var ki0, ko0, r0 : Gate.token*Gate.token*Gate.token = hd answers;
    var ki1, ko1, r1 : Gate.token*Gate.token*Gate.token = hd (tl answers);
    
    x.[(1,  t1)] = ki0;
    x.[(1, !t1)] = ki1;
    x.[(3, val0)] = ko0;
    x.[(3, val1)] = ko1;

    common2();

    common3();
    
    g.[( t1, tau)] = r0;
    g.[(!t1, tau)] = r1;
  }
  
  fun gen_queries2() : Dkc.query list = {
    var x1 : bool = get xc 1;
    var x2 : bool = get xc 2;
    var val:bool = Gate.eval fc (x1, !x2);
    var vis1:bool = x1^^(proj t.[1]);

    common0();
    
    t.[2] = ! x2 ^^ tau;
    
    common1();

    return [((1, vis1), (2, val), false, Gate.tweak vis1 tau)];
  }
  
  fun computeG2(answers:Dkc.answer list) : unit =  {
    var x1 : bool = get xc 1;
    var x2 : bool = get xc 2;
    var val:bool = Gate.eval fc (x1, !x2);
    var vis1:bool = x1^^(proj t.[1]);

    var ki, ko, r : Gate.token*Gate.token*Gate.token = hd answers;

    x.[(1, vis1)] = ki;
    x.[(3, val)] = ko;
    
    common2();
    
    preG.[(!vis1,  tau)] = $Dkc.genRandKey;
    if ((Gate.eval fc (!x1, false) = Gate.eval fc (!x1, true)))
      preG.[(!vis1, !tau)] = proj preG.[(!vis1,  tau)];
    else
      preG.[(!vis1, !tau)] = $Dkc.genRandKey;

    common3();
    
    g.[( vis1,  tau)] = r;
  }
  
  fun gen_queries3() : Dkc.query list = {
    var l1 : bool;
    var l2 : bool;

    common0();

    common1();

    common2();

    l1 = (get xc 1)^^(proj t.[1]);
    l2 = (get xc 2)^^(proj t.[2]);
    preG.[(!l1,  l2)] = $Dkc.genRandKey;
    preG.[( l1, !l2)] = $Dkc.genRandKey;
    preG.[(!l1, !l2)] = $Dkc.genRandKey;

    common3();
    
    return [];
  }

  fun computeG3(answers:Dkc.answer list) : unit = {
    
  }
  
  fun gen_queries(tau:bool) : Dkc.query list = {
    var c : bool;
    var query : Gate.query;
    var ret : Dkc.query list;
    c = $Dbool.dbool;
    l = $Dinter.dinter 1 3;
    (*query := Adv.gen_query();*)
    tau = tau;
    if (c) (fc, xc) = fst query; else (fc, xc) = snd query;
    if (l=1) ret := gen_queries1();
    if (l=2) ret := gen_queries2();
    if (l=3) ret := gen_queries3();
    return ret;
  }
  
  fun get_challenge(answers:Dkc.answer list) : bool = {
    var challenge : bool;
    var gg : functG;
    if (l=1) computeG1(answers);
    if (l=2) computeG2(answers);
    if (l=3) computeG3(answers);
    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    (*challenge := Adv.get_challenge((gg, input, unit));*)
    return challenge;
  }
}.

require import Bitstring.
require import Int.
require import Bool.
require import Pair.
require import Map.
require import Distr.
require import List.

require import Dkc.
require import Gate.
require import GarbleTools.

op get(x:'a*'a, i:int) : 'a = if i = 0 then fst x else snd x.
op set(x:'a*'a, i:int, v:'a) : 'a*'a = if i = 0 then (v, snd x) else (fst x, v).

op enc(
  x:(int*bool, token) map,
  preG:((bool*bool), token) map,
  fc : Gate.funct, a:bool, b:bool) =
Dkc.encode (tweak 0 a b) (proj x.[(0, a)]) (proj x.[(1, b)]) (proj preG.[(a, b)]).

op initG(
  g:((bool*bool), token) map,
  x:(int*bool, token) map,
  preG:((bool*bool), token) map,
  fc : Gate.funct, a:bool, b:bool) =
    g.[(a, b) <- enc x preG fc a b].

op initInput(
  input:Gate.inputG,
  x:(int*bool, token) map,
  xc:Gate.input, i:int) =
    set input i (proj x.[(i, (get xc i))]).

module Wrapper(A:Gate.Adv) : Gate.Adv = {
    fun gen_query() : Gate.query = {
      var r : query;
      return r;
    }
    fun get_challenge(answer: Gate.answer) : bool = {
      var r : bool;
      return r;
    }
}.

module Adv(A:Gate.Adv) : Dkc.Adv = {

  module Adv = Wrapper(A)

  var fc : Gate.funct
  var xc : Gate.input
  var tau : bool
  var l : int

  var input : Gate.inputG
  var g : ((bool*bool), token) map
  var preG : ((bool*bool), token) map
  var x : (int*bool, token) map
  var t : (int, bool) map

  fun common0() : unit = {
    x = Map.empty;
    preG = Map.empty;
    g = Map.empty;
    t = Map.empty;
    t.[0] = $Dbool.dbool;
    t.[1] = $Dbool.dbool;
    t.[2] = false;
  }

  fun initX(i:int, b:bool) : unit = {
    x.[(i, b)] = $Dkc.genRandKeyLast((proj t.[1])^^b);
  }
  fun common1() : unit = {
    initX(0, false);
    initX(0,  true);
    initX(1, false);
    initX(1,  true);
    initX(2, false);
    initX(2,  true);
  }

  fun initPreG(a:bool, b:bool) : unit = {
    preG.[(a, b)] = proj x.[(2, Gate.eval fc (a, b))];
  }
  fun common2() : unit = {
    initPreG(false, false);
    initPreG( true, false);
    initPreG(false,  true);
    initPreG( true,  true);
  }
  
  (*fun initG(a:bool, b:bool) : unit = {
    g.[(a, b)] = Dkc.encode (tweak 0 a b) (proj x.[(0, a)]) (proj x.[(1, b)]) (proj preG.[(a, b)]);
  }
  fun initInput(i:int) : unit = {
    input = set input i (proj x.[(i, (get xc i))]);
  }*)
  fun common3() : unit = {
    g = initG g x preG fc false false;
    g = initG g x preG fc false true;
    g = initG g x preG fc true false;
    g = initG g x preG fc true true;
    input = initInput input x xc 0;
    input = initInput input x xc 1;
    (*initG(false, false);
    initG(false,  true);
    initG( true, false);
    initG( true,  true);
    initInput(0);
    initInput(1);*)
  }

  fun gen_queries1() : Dkc.query list = {
    var x1 : bool = get xc 0;
    var t2 : bool = proj t.[1];
    var val0 : bool = Gate.eval fc (!x1, false);
    var val1 : bool = Gate.eval fc (!x1, true);
    
    common0();
    
    t.[1] = ! x1 ^^ tau;

    common1();

    return [
      ((0,  t2), (1, val0), true, tweak 0 tau   t2 ) ;
      ((0, !t2), (1, val1), true, tweak 0 tau (!t2))
      ];
  }

  fun computeG1(answers:Dkc.answer list) : unit = {
    var x1 : bool = get xc 0;
    var t2 : bool = proj t.[1];
    var val0 : bool = Gate.eval fc (!x1, false);
    var val1 : bool = Gate.eval fc (!x1, true);

    var ki0, ko0, r0 : token*token*token = hd answers;
    var ki1, ko1, r1 : token*token*token = hd (tl answers);
    
    x.[(0,  t2)] = ki0;
    x.[(0, !t2)] = ki1;
    x.[(2, val0)] = ko0;
    x.[(2, val1)] = ko1;

    common2();

    common3();
    
    g.[(tau,  t2)] = r0;
    g.[(tau, !t2)] = r1;
  }
  
  fun gen_queries2() : Dkc.query list = {
    var x1 : bool = get xc 0;
    var x2 : bool = get xc 1;
    var val:bool = Gate.eval fc (x1, !x2);
    var vis1:bool = x1^^(proj t.[0]);

    common0();
    
    t.[1] = ! x2 ^^ tau;
    
    common1();

    return [((0, vis1), (1, val), false, tweak 0 vis1 tau)];
  }
  
  fun computeG2(answers:Dkc.answer list) : unit =  {
    var x1 : bool = get xc 0;
    var x2 : bool = get xc 1;
    var val:bool = Gate.eval fc (x1, !x2);
    var vis1:bool = x1^^(proj t.[0]);

    var ki, ko, r : token*token*token = hd answers;

    x.[(0, vis1)] = ki;
    x.[(2, val)] = ko;
    
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

    common0();

    common1();
    
    return [];
  }

  fun computeG3(answers:Dkc.answer list) : unit = {
    var l1 : bool;
    var l2 : bool;

    common2();

    l1 = (get xc 0)^^(proj t.[0]);
    l2 = (get xc 1)^^(proj t.[1]);
    preG.[(!l1,  l2)] = $Dkc.genRandKey;
    preG.[( l1, !l2)] = $Dkc.genRandKey;
    preG.[(!l1, !l2)] = $Dkc.genRandKey;

    common3();
  }
  
  fun preInit() : unit = {
    l = $Dinter.dinter 0 2;
  }

  fun gen_queries(info:bool) : Dkc.query list = {
    var c : bool;
    var query : Gate.query;
    var ret : Dkc.query list;
    c = $Dbool.dbool;
    query := Adv.gen_query();
    tau = info;
    if (c) (fc, xc) = fst query; else (fc, xc) = snd query;
    if (l=0) ret := gen_queries1();
    if (l=1) ret := gen_queries2();
    if (l=2) ret := gen_queries3();
    return ret;
  }
  
  fun get_challenge(answers:Dkc.answer list) : bool = {
    var challenge : bool;
    var gg : Gate.functG;
    if (l=0) computeG1(answers);
    if (l=1) computeG2(answers);
    if (l=2) computeG3(answers);
    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge := Adv.get_challenge((gg, input, tt));
    return challenge;
  }
}.

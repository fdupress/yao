require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.

require import Dkc. import Dkc.
require import AdvGate.
require import Gate.

  module DkcInline : Dkc_t = {
    var b : bool
    var ksec : key
    var r : (int*bool, key) map
    var kpub : (int*bool, key) map
    var used : tweak set

    fun preInit() : unit = {
      b = $bsample;
    }
      
    fun initialize() : bool = {
      ksec = $genRandKey;
      return ksec.[0];
    }

    fun get_challenge() : bool = {
      return b;
    }
    
    fun encrypt(q:query) : answer = {
      var keya : key;
      var keyb : key;
      var msg : msg;
      var i : int*bool;
      var j : int*bool;
      var pos : bool;
      var t : tweak;
      var out : answer;
      (i, j, pos, t) = q;
      out = bad;
      if (! ((mem t used) || ((fst j) <= (fst i))))
      {
        used = add t used;
        if (! (in_dom i kpub)) kpub.[i] = $genRandKeyLast (snd i);
        if (! (in_dom j kpub)) kpub.[j] = $genRandKeyLast (snd j);
        if (! (in_dom i r)) r.[j] = $genRandKey;
        if (pos = true) {
          keya = ksec;
          keyb = proj kpub.[i];
        } else {
          keyb = ksec;
          keya = proj kpub.[i];
        }
        if (b = true) msg = proj kpub.[j]; else msg = proj r.[j];
        out = (proj kpub.[i], proj kpub.[j], encode t keya keyb msg);
      }
      return out;
    }
  }.

module Adv = {
    fun gen_query() : Gate.query = {
      var r : query;
      return r;
    }
    fun get_challenge(answer: Gate.answer) : bool = {
      var r : bool;
      return r;
    }
}.

module Game = {

  (*BEGIN Dkc var*)
    var dkc_b : bool
    var dkc_ksec : key
    var dkc_r : (int*bool, key) map
    var dkc_kpub : (int*bool, key) map
    var dkc_used : tweak set
  (*END Dkc var*)

  (*BEGIN Adv var*)
    var adv_fc : Gate.funct
    var adv_xc : Gate.input
    var adv_tau : bool
    var adv_l : int

    var adv_input : Gate.inputG
    var adv_g : ((bool*bool), token) map
    var adv_preG : ((bool*bool), token) map
    var adv_x : (int*bool, token) map
    var adv_t : (int, bool) map
  (*END Adv var*)

  fun work() : bool = {
    (*BEGIN Game.Work var*)
      var queries : query list;
      var answers : answer list;
      var i : int;
      var info : bool;
      var advChallenge : bool;
      var realChallenge : bool;
      var nquery : int;
      var answer : answer;
    (*END Game.Work var*)

    (*BEGIN Adv.gen_queries var*)
      var adv_gen_c : bool;
      var adv_gen_query : Gate.query;
      var adv_gen_ret : Dkc.query list;
    (*END Adv.gen_queries var*)

    (*BEGIN Adv.gen_queries1 Adv.computeG1 var*)
      var adv1_x1 : bool;
      var adv1_t2 : bool;
      var adv1_val0 : bool;
      var adv1_val1 : bool;
      var adv1_ki0, adv1_ko0, adv1_r0 : token*token*token;
      var adv1_ki1, adv1_ko1, adv1_r1 : token*token*token;
    (*END Adv.gen_queries1 Adv.computeG1 var*)

    (*BEGIN Adv.gen_queries2 Adv.computeG2 var*)
      var adv2_x1 : bool;
      var adv2_x2 : bool;
      var adv2_val:bool;
      var adv2_vis1:bool;
    (*END Adv.gen_queries2 Adv.computeG2 var*)

    (*BEGIN Adv.gen_challenge var*)
      var adv_gench_challenge : bool;
      var adv_gench_gg : Gate.functG;
    (*END Adv.gen_challenge var*)



    (*BEGIN D.initialize()*)
      dkc_ksec = $genRandKey;
      info = dkc_ksec.[0];
    (*END D.initialize()*)

    (*BEGIN A.gen_queries(info)*)
      adv_gen_c = $Dbool.dbool;
      adv_gen_query := Adv.gen_query();
      adv_tau = info;
      if (adv_gen_c) (adv_fc, adv_xc) = fst adv_gen_query;
      else (adv_fc, adv_xc) = snd adv_gen_query;
      if (adv_l=0) {
        (*BEGIN A.gen_queries1()*)
          adv_gen1_x1 = get adv_xc 0;
          adv_gen1_t2 = proj adv_t.[1];
          adv_gen1_val0 = Gate.eval adv_fc (!adv_gen1_x1, false);
          adv_gen1_val1 = Gate.eval adv_fc (!adv_gen1_x1, true);

          (*BEGIN common0()*)
            adv_x = Map.empty;
            adv_preG = Map.empty;
            adv_g = Map.empty;
            adv_t = Map.empty;
            adv_t.[0] = $Dbool.dbool;
            adv_t.[1] = $Dbool.dbool;
            adv_t.[2] = false;
          (*END common0()*)
    
          adv_t.[1] = ! adv_gen1_x1 ^^ adv_tau;

          (*BEGIN common1()*)
            adv_x.[(0, false)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(0, true)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(1, false)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(1, true)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(2, false)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(2, true)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
          (*END common1()*)

          adv_gen_ret = [
            ((0,  adv_gen1_t2), (1, adv_gen1_val0), true, tweak 0 adv_tau   adv_gen1_t2 ) ;
            ((0, !adv_gen1_t2), (1, adv_gen1_val1), true, tweak 0 adv_tau (!adv_gen1_t2))
          ];
        (*END A.gen_queries1()*)
      }
      if (adv_l=1) {
        (*BEGIN A.gen_queries2()*)
          adv_gen2_x1 = get adv_xc 0;
          adv_gen2_x2 = get adv_xc 1;
          adv_gen2_val = Gate.eval adv_fc (adv_gen2_x1, !adv_gen2_x2);
          adv_gen2_vis1 = adv_gen2_x1^^(proj adv_t.[0]);

          (*BEGIN common0()*)
            adv_x = Map.empty;
            adv_preG = Map.empty;
            adv_g = Map.empty;
            adv_t = Map.empty;
            adv_t.[0] = $Dbool.dbool;
            adv_t.[1] = $Dbool.dbool;
            adv_t.[2] = false;
          (*END common0()*)
    
          adv_t.[1] = ! adv_gen2_x2 ^^ adv_tau;
    
          (*BEGIN common1()*)
            adv_x.[(0, false)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(0, true)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(1, false)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(1, true)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(2, false)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
            adv_x.[(2, true)] = $Dkc.genRandKeyLast((proj adv_t.[1])^^adv_b);
          (*END common1()*)

          adv_gen_ret = [((0, adv_gen2_vis1), (1, adv_gen2_val), false, tweak 0 adv_gen2_vis1 adv_tau)];
        (*END A.gen_queries2()*)
      }
      (*if (adv_l=2) {
        (*BEGIN A.gen_queries3()*)
          adv_gen_ret := gen_queries3();
        (*END A.gen_queries3()*)
      }*)
      queries = adv_gen_ret;
    (*END A.gen_queries(info)*)

    nquery = List.length queries;
    answers = [];
    i = 0;
    while (i < nquery)
    {
      answer := D.encrypt (List.hd queries);
      answers = answer::answers;
      queries = List.tl queries;
    }

    (*BEGIN D.get_challenge()*)
      realChallenge = dkc_b;
    (*END D.get_challenge()*)

    (*BEGIN A.get_challenge(answers)*)
      if (adv_l=0) {
        (*BEGIN A.computeG1()*)
          adv1_ki0, adv1_ko0, adv1_r0 = hd answers;
          adv1_ki1, adv1_ko1, adv1_r1 = hd (tl answers);

          adv_x.[(0,  adv1_t2)] = adv1_ki0;
          adv_x.[(0, !adv1_t2)] = adv1_ki1;
          adv_x.[(2, adv1_val0)] = adv1_ko0;
          adv_x.[(2, adv1_val1)] = adv1_ko1;

          common2();

          common3();
          
          adv_g.[(adv_tau,  t2)] = adv1_r0;
          adv_g.[(adv_tau, !t2)] = adv1_r1;
        (*END A.computeG1()*)
      }
      if (adv_l=1) {
        (*BEGIN A.computeG2()*)
          computeG2(answers);
        (*END A.computeG2()*)
      }
    (*if (adv_l=2) computeG3(answers);*)
      adv_gench_gg = (proj adv_g.[(false, false)], proj adv_g.[(false, true)], proj adv_g.[(true, false)], proj adv_g.[(true, true)]);
      challenge := Adv.get_challenge((adv_gench_gg, adv_input, adv_tt));
      advChallenge = adv_gench_challenge;
    (*END A.get_challenge(answers)*)

    return advChallenge = realChallenge;
  }
}.
require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.

theory Dkc.
  type number = bitstring.

  type key = number.
  type msg = number.
  type cipher = number.
  type tweak = number.

  op k : int.
  op tau : int.
  op sb : int.

  op genRandKey : key distr.
  op genRandKeyLast : bool -> key distr.

  op encode : tweak -> key -> key -> msg -> cipher.
  op decode : tweak -> key -> key -> cipher -> msg.
  axiom inverse :
    forall (t:tweak),
    forall (k1:key),
    forall (k2:key),
    forall (m:msg),
    decode t k1 k2 (encode t k1 k2 m) = m.

  type query = (int*bool)*(int*bool)*bool*tweak.
  type answer = key*key*cipher.

  op bsample : bool distr.
  op bad : answer.

  module type Dkc_t = {
    fun preInit() : unit
    fun initialize() : bool
    fun encrypt(q:query) : answer
    fun get_challenge() : bool
  }.

  module type Adv = {
    fun preInit() : unit
    fun gen_queries(info:bool) : (query list)
    fun get_challenge(answers: (answer list)) : bool
  }.

  module Dkc : Dkc_t = {
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

  module Game(D:Dkc_t, A:Adv) = {

    fun preInit() : unit = {
      D.preInit();
      A.preInit();
    }

    fun work() : bool = {
      var queries : query list;
      var answers : answer list;
      var i : int;
      var info : bool;
      var advChallenge : bool;
      var realChallenge : bool;
      var nquery : int;
      var answer : answer;
      info := D.initialize();
      queries := A.gen_queries(info);
      nquery = List.length queries;
      answers = [];
      i = 0;
      while (i < nquery)
      {
        answer := D.encrypt (List.hd queries);
        answers = answer::answers;
        queries = List.tl queries;
      }
      realChallenge := D.get_challenge();
      advChallenge := A.get_challenge(answers);
      return advChallenge = realChallenge;
    }
    
    fun main() : bool = {
      var r : bool;
      preInit();
      r := work();
      return r;
    }
  }.

  axiom DKCSec :
    forall (epsilon:real),
    forall (ADV<:Adv),
    forall &m,
      (epsilon > 0%r) => (Pr[Game(Dkc, ADV).main()@ &m:res] < epsilon).
end Dkc.
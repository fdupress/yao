require import Bitstring.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.
require import Array.
require import Distr.
require import MyRand.

theory DKC.
  type number = bitstring.

  type key = number.
  type msg = number.
  type cipher = number.
  type tweak = number.

  op k : int.
  op tau : int.
  op sb : int.

  op genRandKey = Dbitstring.dbitstring k.
  op genRandKeyLast = Dbitstringlast.dbitstringlast k.

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

  op defaultQ : query.
  op bad : answer.

  module type Dkc_t = {
    fun preInit() : unit
    fun initialize() : bool
    fun encrypt(q:query) : answer
    fun get_challenge() : bool
  }.

  module type Adv = {
    fun preInit() : unit
    fun gen_queries(info:bool) : (query array)
    fun get_challenge(answers: (answer array)) : bool
  }.

  module type AdvAda(DKC:Dkc_t) = {
    fun preInit() : unit {}
    fun work(info:bool) : bool {DKC.encrypt}
  }.

  module Dkc : Dkc_t = {
    var b : bool
    var ksec : key
    var r : (int*bool, msg) map
    var kpub : (int*bool, key) map
    var used : tweak set

    fun preInit() : unit = {
      b = $Dbool.dbool;
    }
      
    fun initialize() : bool = {
      var t : bool;
      t = $Dbool.dbool;
      ksec = $genRandKeyLast t;
      kpub = Map.empty;
      r = Map.empty;
      return t;
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
        if (pos) {
          keya = ksec;
          keyb = proj kpub.[i];
        } else {
          keyb = ksec;
          keya = proj kpub.[i];
        }
        if (b) msg = proj kpub.[j]; else msg = proj r.[j];
        out = (proj kpub.[i], proj kpub.[j], encode t keya keyb msg);
      }
      return out;
    }
  }.

  module type Exp = {
    fun preInit() : unit
    fun work() : bool
    fun main() : bool
  }.

  module Game(D:Dkc_t, A:Adv) : Exp = {

    fun preInit() : unit = {
      D.preInit();
      A.preInit();
    }

    fun work() : bool = {
      var queries : query array;
      var answers : answer array;
      var a : answer array;
      var i : int;
      var info : bool;
      var advChallenge : bool;
      var realChallenge : bool;
      var nquery : int;
      var answer : answer;
      info = D.initialize();
      queries = A.gen_queries(info);
      nquery = Array.length queries;
      answers = Array.init nquery bad;
      i = 0;
      while (i < nquery)
      {
        answers.[i] = D.encrypt (queries.[i]);
        i = i + 1;
      }
      advChallenge = A.get_challenge(answers);
      realChallenge = D.get_challenge();
      return advChallenge = realChallenge;
    }
    
    fun main() : bool = {
      var r : bool;
      preInit();
      r = work();
      return r;
    }
  }.

  module GameAda(D:Dkc_t, Adv:AdvAda) = {

    module A = Adv(Dkc)

    fun preInit() : unit = {
      D.preInit();
      A.preInit();
    }

    fun work() : bool = {
      var info : bool;
      var advChallenge : bool;
      var realChallenge : bool;
      info = D.initialize();
      advChallenge = A.work(info);
      realChallenge = D.get_challenge();
      return advChallenge = realChallenge;
    }
    
    fun main() : bool = {
      var r : bool;
      preInit();
      r = work();
      return r;
    }
  }.



  axiom Security :
    exists (epsilon:real), epsilon > 0%r /\
      forall (A<:Adv), forall &m,
        `|2%r * Pr[Game(Dkc, A).main()@ &m:res] - 1%r| <
          epsilon.

end DKC.

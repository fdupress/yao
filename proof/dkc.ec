require import Bitstring.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.
require import Array.
require import Distr.

type t = bitstring.

theory DKC_Abs.

  op genRandKey : t distr.
  op genRandKeyLast : t distr.
  op addLast : t -> bool -> t.

  op encode : t -> t -> t -> t -> t.
  op decode : t -> t -> t -> t -> t.
end DKC_Abs.

theory DKC.
  type t = bitstring.

  op k : int.
  axiom kVal : k > 1.

  op genRandKey = Dbitstring.dbitstring k.
  op genRandKeyLast = Dbitstring.dbitstring (k-1).
  op addLast : t -> bool -> t .

  op encode : t -> t -> t -> t -> t.
  op decode : t -> t -> t -> t -> t.
end DKC.

theory DKC_Sec.

  clone export DKC_Abs.

  type query = (int*bool)*(int*bool)*bool*t.
  type answer = t*t*t.

  op defaultQ : query.
  op bad : answer.

  module type Dkc_t = {
    fun preInit() : unit
    fun initialize() : bool
    fun encrypt(q:query) : answer
    fun get_challenge() : bool
  }.

  module type Adv_t = {
    fun preInit() : unit
    fun gen_queries(info:bool) : (query array)
    fun get_challenge(answers: (answer array)) : bool
  }.

  module Dkc : Dkc_t = {
    var b : bool
    var ksec : t
    var r : (int*bool, t) map
    var kpub : (int*bool, t) map
    var used : t set

    fun preInit() : unit = {
      b = $Dbool.dbool;
    }
      
    fun initialize() : bool = {
      var t : bool;
      t = $Dbool.dbool;
      ksec = $genRandKeyLast;
      ksec = addLast ksec t;
      kpub = Map.empty;
      used = Set.empty;
      r = Map.empty;
      return t;
    }

    fun get_challenge() : bool = {
      return b;
    }
    
    fun encrypt(q:query) : answer = {
      var keya : t;
      var keyb : t;
      var msg : t;
      var i : int*bool;
      var j : int*bool;
      var pos : bool;
      var t : t;
      var out : answer;
      var temp : t;
      (i, j, pos, t) = q;
      out = bad;
      if ((!(mem t used)) /\ ((fst j) > (fst i)))
      {
        used = add t used;
        if (! (in_dom i kpub)) {
          temp = $genRandKeyLast;
          kpub.[i] = addLast temp (snd i);
        }
        if (! (in_dom j kpub)) {
          temp = $genRandKeyLast;
          kpub.[j] = addLast temp (snd j);
        }
        if (! (in_dom j r))
          r.[j] = $genRandKey;
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

  module Game(D:Dkc_t, A:Adv_t) : Exp = {

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
      answers = Array.create nquery bad;
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

  module type AdvAda_t(DKC:Dkc_t) = {
    fun preInit() : unit {}
    fun work(info:bool) : bool {DKC.encrypt}
  }.

  module GameAda(D:Dkc_t, Adv:AdvAda_t) : Exp = {

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

end DKC_Sec.

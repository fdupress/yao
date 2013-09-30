require import Bitstring.
require import Map.
require import FSet.
require import Pair.
require import Int.
require import Real.
require import Bool.
require import Array.
require import Distr.

type t = bitstring.

theory DKC_Abs.
  op genRandKey: t distr.
  op genRandKeyLast: t distr.
  op addLast: t -> bool -> t.
  op lsb: t -> bool.

  op E: t -> t -> t -> t -> t.
  op D: t -> t -> t -> t -> t.

  axiom lsb_addLast x b: lsb (addLast x b) = b.
end DKC_Abs.

theory DKC.
  type t = bitstring.

  op k : int.
  axiom kVal : k > 1.

  op genRandKey = Dbitstring.dbitstring k.
  op genRandKeyLast = Dbitstring.dbitstring (k-1).
  op addLast : t -> bool -> t.
  op lsb: t -> bool.

  op E: t -> t -> t -> t -> t.
  op D: t -> t -> t -> t -> t.

  axiom lsb_addLast x b: lsb (addLast x b) = b.
end DKC.

theory DKC_Sec.
  clone export DKC_Abs.

  type query = (int * bool) * (int * bool) * bool * t.
  type answer = t * t * t.

  op defaultQ: query. (* Why use this instead of option? What happens if the adversary queries defaultQ? *)
  op bad: answer.     (* Same question: can any query other than defaultQ return bad? *)

  module type Dkc_t = {
    fun preInit(): unit
    fun initialize(): bool
    fun encrypt(q:query): answer
    fun get_challenge(): bool
  }.

  module type Adv_t = {
    fun preInit(): unit
    fun gen_queries(info:bool): query array
    fun get_challenge(answers:answer array) : bool
  }.

  module DKCm = {
    var b:bool
    var ksec:t
    var r:(int * bool,t) map
    var kpub:(int * bool,t) map
    var used:t set
  }.

  module Dkc : Dkc_t = {
    fun preInit(): unit = {
      DKCm.b = $Dbool.dbool;
    }
      
    fun initialize() : bool = {
      var t : bool;
      t = $Dbool.dbool;
      DKCm.ksec = $genRandKeyLast;
      DKCm.ksec = addLast DKCm.ksec t;
      DKCm.kpub = Map.empty;
      DKCm.used = FSet.empty;
      DKCm.r = Map.empty;
      return t;
    }

    fun get_challenge() : bool = {
      return DKCm.b;
    }

    fun get_k(i:int * bool): t = {
      var r:t;

      r = $genRandKeyLast;
      if (!in_dom i DKCm.kpub) DKCm.kpub.[i] = addLast r (snd i);
      return proj DKCm.kpub.[i];
    }

    fun get_r(i:int * bool): t = {
      var r:t;

      r = $genRandKey;
      if (!in_dom i DKCm.kpub) DKCm.kpub.[i] = r;
      return proj DKCm.kpub.[i];
    }

    fun encrypt(q:query): answer = {
      var ka, kb, ki, kj, rj, msg, t:t;
      var i, j:int * bool;
      var pos:bool;
      var out:answer;

      (i,j,pos,t) = q;
      out = bad;
      if (!(mem t DKCm.used) /\ fst i < fst j)
      {
        DKCm.used = add t DKCm.used;
        ki = get_k(i);
        kj = get_k(j);
        rj = get_r(j);

        (ka,kb) = if pos then (DKCm.ksec,ki) else (ki,DKCm.ksec);
        msg = if (DKCm.b) then kj else rj;
        out = (ki,kj,E t ka kb msg);
      }
      return out;
    }
  }.

  lemma get_kL:
    weight genRandKeyLast = 1%r =>
    islossless Dkc.get_k.
  proof strict.
  by intros=> genRandKeyLastL; fun; wp; rnd.
  qed.

  lemma get_rL:
    weight genRandKey = 1%r =>
    islossless Dkc.get_r.
  proof strict.
  by intros=> genRandKeyL; fun; wp; rnd.
  qed.

  lemma encryptL:
    weight genRandKey = 1%r =>
    weight genRandKeyLast = 1%r =>
    islossless Dkc.encrypt.
  proof strict.
  intros genRandKeyL genRandKeyLastL; fun; seq 2: (q = (i,j,pos,t) /\ out = bad)=> //; first by wp.
  by if=> //; wp; call (get_rL _)=> //; do !(call (get_kL _)=> //); wp.
  by hoare; wp.
  qed.

  module type Exp = {
    fun preInit():unit
    fun work():bool
    fun main():bool
  }.

  module type Batch_t = {
    fun encrypt(qs:query array): answer array
  }.

  module BatchDKC (D:Dkc_t): Batch_t = {
    fun encrypt(qs:query array): answer array = {
      var i, n:int;
      var answers:answer array;

      i = 0;
      n = length qs;
      answers = Array.create n bad;
      while (i < n)
      {
        answers.[i] = D.encrypt(qs.[i]);
        i = i + 1;
      }

      return answers;
    }
  }.

  lemma encryptBatchL (D <: Dkc_t { BatchDKC }):
    islossless D.encrypt =>
    islossless BatchDKC(D).encrypt.
  proof strict.
  intros=> encryptL; fun.
  while true (n - i);
    first by intros=> z; wp; call encryptL; skip; smt.
  by wp; skip; smt.
  qed.

  module Game(D:Dkc_t, A:Adv_t) : Exp = {
    module B = BatchDKC(D)

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
      answers = B.encrypt(queries);
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

  (** Adaptive adversary: is it possible to find an expressible
      condition on A.work that guarantees the desired equivalence?
   INSIGHT: it looks like it should be sufficient to look at Query
      to prove the adaptive -> non-adaptive result:
        1) it is never called with a = b;
        2) for a given g, it is called three times with rnd = false,
           but different (alpha,beta) pairs (hence different tweaks);
        3) for a given g, it is called once with rnd = true (fresh tweak, random j)
        4) for different g, the tweaks are necessarily different
      **5) the queries (i,j,pos,T) depend only on a, b, g, the two constants alpha and beta,
           and pre-initialized variables (the circuit and the t.[i]s) *)
  module type AdvAda_t(DKC:Dkc_t) = {
    fun preInit() : unit {}
    fun work(info:bool) : bool {DKC.encrypt}
  }.

  module GameAda(D:Dkc_t, Adv:AdvAda_t): Exp = {
    module A = Adv(Dkc)

    fun preInit(): unit = {
      D.preInit();
      A.preInit();
    }

    fun work(): bool = {
      var info: bool;
      var advChallenge: bool;
      var realChallenge: bool;

      info = D.initialize();

      advChallenge = A.work(info);
      realChallenge = D.get_challenge();
      return advChallenge = realChallenge;
    }

    fun main(): bool = {
      var r: bool;

      preInit();
      r = work();
      return r;
    }
  }.
end DKC_Sec.

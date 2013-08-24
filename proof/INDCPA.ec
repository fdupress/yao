require import Real.
require import Pair.
require import Bool.

(** begin def *)
theory INDCPA.

  theory Scheme.
    type plain.
    type cipher.

    op queryValid : plain*plain -> bool.
    op enc : plain -> cipher distr.
  end Scheme.

  module type Adv_t = {
    fun gen_query() : query
    fun get_challenge(cipher:cipher) : bool
  }.

  module Game(ADV:Adv_t) = {
    fun main() : bool = {
      var query : plain*plain;
      var p : plain;
      var c : cipher;
      var b, adv, ret : bool;
    
      query = ADV.gen_query();
      if (queryValid query)
      {
        b = $Dbool.dbool;
        if (b) p = fst query;
        else   p = snd query;
        c = $enc p;
        adv = ADV.get_challenge(c);
        ret = (b = adv);
      }
      else
        ret = $Dbool.dbool;
      return ret;
    }
  }.
end INDCPA.
(** end def *)
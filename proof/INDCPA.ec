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
    fun gen_query() : Scheme.plain*Scheme.plain
    fun get_challenge(cipher:Scheme.cipher) : bool
  }.

  module Game(ADV:Adv_t) = {
    fun main() : bool = {
      var query : Scheme.plain*Scheme.plain;
      var p : Scheme.plain;
      var c : Scheme.cipher;
      var b, adv, ret : bool;
    
      query = ADV.gen_query();
      if (Scheme.queryValid query)
      {
        b = $Dbool.dbool;
        if (b) p = fst query;
        else   p = snd query;
        c = $Scheme.enc p;
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
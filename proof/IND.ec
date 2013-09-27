require import Real.
require import Pair.
require import Bool.

(** begin def *)
theory IND.

  theory Scheme.
    type plain.
    type cipher.

    op enc : plain -> cipher distr.
    op queryValid : plain*plain -> bool.
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
      var b, b', ret : bool;
    
      query = ADV.gen_query();
      if (Scheme.queryValid query)
      {
        b = ${0,1};
        p = if b then fst query else snd query;
        c = $Scheme.enc p;
        b' = ADV.get_challenge(c);
        ret = (b = b');
      }
      else
        ret = ${0,1};
      return ret;
    }
  }.
end IND.
(** end def *)
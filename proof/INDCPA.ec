require import Real.
require import Pair.
require import Bool.

theory INDCPA_Scheme.
  type query.
  type answer.
  type random.

  op queryValid : query*query -> bool.
  op work : query -> random -> answer.
end INDCPA_Scheme.

theory INDCPA_Def.

  clone import INDCPA_Scheme.

  type queries = query * query.

  module type Adv_t = {
    fun gen_query() : query*query
    fun get_challenge(answer:answer) : bool
  }.

  module type Rand_t = { fun gen(query:query) : random }.

  module Game(Rand:Rand_t, ADV:Adv_t) = {
    fun main() : bool = {
      var query : query*query;
      var q : query;
      var r : random;
      var answer : answer;
      var adv, real : bool;
      var ret : bool;
      var b : bool;
    
      query = ADV.gen_query();
      if (queryValid query)
      {
        b = $Dbool.dbool;
        if (b)
          q = fst query;
        else
          q = snd query;
        r = Rand.gen(q);
        adv = ADV.get_challenge(work q r);
        ret = (b = adv);
      }
      else
        ret = $Dbool.dbool;
      return ret;
    }
  }.
end INDCPA_Def.
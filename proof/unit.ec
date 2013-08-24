require import Real.
require import Pair.
require import Bool.
require import INDCPA.

(** begin unitdef *)
clone INDCPA.Scheme as UNIT_Scheme with type plain = unit.

clone INDCPA as UNIT with theory Scheme = UNIT_Scheme.
(** end unitdef *)

(** begin unitGame *)
module Rnd(ADV:UNIT.Adv_t) = {
  fun main() : bool = {
    var query : UNIT.query;
    var c : UNIT.Scheme.cipher;
    var b, adv, ret : bool;
    query = ADV.gen_query();
    if (UNIT.Scheme.queryValid query)
    {
      c = $UNIT.Scheme.enc tt;
      adv = ADV.get_challenge(c);
      b = $Dbool.dbool;
      ret = (b = adv);
    }
    else
      ret = $Dbool.dbool;
    return ret;
  }
}.
(** end unitGame *)

(** begin uniteq *)
lemma unitEq (A<:UNIT.Adv_t) :
    equiv[UNIT.Game(A).main ~ Rnd(A).main : ={glob A} ==> ={res}].
(** end uniteq *)
fun.
seq 1 1 : (={glob A,query});
  first by call (_: ={glob A} ==> ={res, glob A});first by fun true.
if=> //;last by rnd.
swap{2} 3 -2.
wp;(call (_: ={glob A, cipher}==> ={res})=> //;first by fun true=> //);rnd;wp;rnd;skip.
intros &1;cut : query{1} = (tt, tt) by (elim/tuple2_ind query{1};smt);smt.
qed.

(** begin unitpr *)
lemma unitPr &m (A<:UNIT.Adv_t) :
  islossless A.gen_query =>
  islossless A.get_challenge =>
  mu (UNIT.Scheme.enc tt) Fun.cpTrue = 1%r =>
    Pr[Rnd(A).main() @ &m : res] = 1%r / 2%r.
(** end unitpr *)
intros ll1 ll2 llenc.
bdhoare_deno (_: true)=> //;fun.
seq 1 : true (1%r) (1%r / 2%r) (0%r) (1%r)=> //;
  first by call (_:true==>true)=> //.
by (if;wp;rnd;first call (_:true ==> true)=> //;(rnd;first smt));
  skip;progress;rewrite Dbool.mu_def /Distr.charfun //;case result=> //.
qed.

(** begin goal *)
lemma goal &m (A<:UNIT.Adv_t) :
  islossless A.gen_query =>
  islossless A.get_challenge =>
  mu (UNIT.Scheme.enc tt) Fun.cpTrue = 1%r =>
    Pr[UNIT.Game(A).main() @ &m : res] = 1%r / 2%r.
proof.
  intros ll1 ll2 llenc.
  rewrite -(unitPr &m A)=> //.
  equiv_deno (unitEq A)=> //.
qed.
(** end goal *)
require import Bitstring.
require import List.
require import Map.
require import FSet.
require import Pair.
require import Int.
require import Bool.
require import Array.

require import GarbleTools.
require import PreProof.

require import Reduction.
require import ReductionAda.

equiv adaEq (ADV <: PrvIndSec.Adv_t{Red, RedAda, DKCS.Dkc}):
      DKCS.Game(DKCS.Dkc, Red(ADV)).main ~
      DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).main
        : (glob ADV){1} = (glob ADV){2} ==> res{1} = res{2}.
proof strict.
(** Preinitialization *)
fun; seq 1 1: (={glob ADV, DKCS.Dkc.b} /\ Red.l{1} = RedAda.l{2} /\ 0 <= Red.l{1} < Cst.bound).
  call (_: true ==> ={DKCS.Dkc.b} /\ Red.l{1} = RedAda.l{2} /\ 0 <= Red.l{1} < Cst.bound)=> //;
  fun;
    call (_: true ==> Red.l{1} = RedAda.l{2} /\ 0 <= Red.l{1} < Cst.bound); first by fun; rnd; skip; smt.
    by call (_: true ==> ={DKCS.Dkc.b}); first by fun; eqobs_in.
(** Experiment *)
call (_: ={glob ADV, DKCS.Dkc.b} /\ Red.l{1} = RedAda.l{2} /\ 0 <= Red.l{1} < Cst.bound ==> ={res})=> //;
fun; inline Red(ADV).gen_queries DKCS.GameAda(DKCS.Dkc, RedAda(ADV)).A.work.
seq  2  2: (={glob ADV, glob DKCS.Dkc, info0, info} /\
            Red.l{1} = RedAda.l{2} /\
            0 <= Red.l{1} < Cst.bound);
  first by wp; call (_: ={DKCS.Dkc.b} ==> ={glob DKCS.Dkc, res}); first by fun; wp; rnd; rnd.
seq 1 1: (={glob ADV, glob DKCS.Dkc, info0} /\
            Red.l{1} = RedAda.l{2} /\
            Red.query{1} = RedAda.query{2} /\
            0 <= Red.l{1} < Cst.bound);
  first by call (_: true).
case (!PrvIndSec.Scheme.queryValid Red.query){1}.
  (** Invalid query *)
  inline Red(ADV).get_challenge.
  rcondf{1} 19; first by intros=> &m; wp; while true; do !(wp; call (_: true ==> true)=> //); wp; rnd.
  rcondf{2} 11; first by intros=> &m; wp; rnd.
  call (_: ={DKCS.Dkc.b})=> //; wp; rnd.
    (* The rest is irrelevant *)
    conseq* (_: ={DKCS.Dkc.b} ==> ={DKCS.Dkc.b})=> //.
      wp; while{1} true (nquery - i){1};
        first by intros=> &m z; wp; call (_: true ==> true); [by apply (DKCS.encryptL _); smt | skip; smt].
      wp; call{1} (garble1L ADV).
      by wp; rnd; skip; smt.
(** Valid query *)
inline Red(ADV).get_challenge.
rcondt{1} 19; first by intros=> &m; wp; while true; do !(wp; call (_: true ==> true)=> //); wp; rnd; skip; smt.
rcondt{2} 11; first by intros=> &m; wp; rnd; skip; smt.
seq  0  0: (={glob ADV, glob DKCS.Dkc, info0} /\
            Red.l{1} = RedAda.l{2} /\
            0 <= Red.l{1} < Cst.bound /\
            Red.query{1} = RedAda.query{2} /\
            PrvIndSec.Scheme.queryValid Red.query{1});
  first by skip; smt.
seq 10 10: (={glob ADV, glob DKCS.Dkc} /\
            Red.l{1} = RedAda.l{2} /\
            Red.query{1} = RedAda.query{2} /\
            Red.c{1} = RedAda.c{2} /\
            Red.fc{1} = RedAda.fc{2} /\
            Red.xc{1} = RedAda.xc{2} /\
            Red.n{1} = RedAda.n{2} /\
            Red.m{1} = RedAda.m{2} /\
            Red.q{1} = RedAda.q{2} /\
            Red.aa{1} = RedAda.aa{2} /\
            Red.bb{1} = RedAda.bb{2} /\
            Red.gg{1} = RedAda.gg{2} /\
            Red.pp{1} = RedAda.pp{2} /\
            Red.t{1} = RedAda.t{2} /\
            Red.v{1} = RedAda.v{2} /\
            Red.yy{1} = RedAda.yy{2} /\
            Red.xx{1} = RedAda.xx{2} /\
            Red.randG{1} = RedAda.randG{2} /\
            Red.tau{1} = RedAda.tau{2} /\
            length Red.v{1} = Red.n{1} + Red.q{1} /\
            length Red.t{1} = Red.n{1} + Red.q{1} /\
            0 <= Red.l{1} < Red.n{1} + Red.q{1}).
  wp; rnd; wp; skip.
    intros=> &1 &2 [[eqAdv [eqDkc eqInfo]] [eqL [[l_lb l_ub] [eqQuery validQuery]]]];
      generalize validQuery; rewrite /PrvIndSec.Scheme.queryValid /PrvInd_Circuit.Scheme.queryValid;
      intros=> Let; elim Let=> {Let} validCircuit1 [validCircuit2 H] {H}; generalize validCircuit1 validCircuit2;
      rewrite /PrvInd_Circuit.Garble.functCorrect /functCorrect /validCircuit=> validCircuit1 validCircuit2;
      generalize eqQuery l_ub l_lb eqL eqInfo eqDkc eqAdv;
      progress=> //; smt. (* Well... that was fun *)
seq  1  0: (={glob ADV, glob DKCS.Dkc} /\
            Red.l{1} = RedAda.l{2} /\
            Red.query{1} = RedAda.query{2} /\
            Red.c{1} = RedAda.c{2} /\
            Red.fc{1} = RedAda.fc{2} /\
            Red.xc{1} = RedAda.xc{2} /\
            Red.n{1} = RedAda.n{2} /\
            Red.m{1} = RedAda.m{2} /\
            Red.q{1} = RedAda.q{2} /\
            Red.aa{1} = RedAda.aa{2} /\
            Red.bb{1} = RedAda.bb{2} /\
            Red.gg{1} = RedAda.gg{2} /\
            Red.pp{1} = RedAda.pp{2} /\
            Red.t{1} = RedAda.t{2} /\
            Red.v{1} = RedAda.v{2} /\
            Red.yy{1} = RedAda.yy{2} /\
            Red.xx{1} = RedAda.xx{2} /\
            Red.randG{1} = RedAda.randG{2} /\
            Red.tau{1} = RedAda.tau{2} /\
            Red.queries{1} = Array.empty /\
            length Red.v{1} = Red.n{1} + Red.q{1} /\
            length Red.t{1} = Red.n{1} + Red.q{1} /\
            0 <= Red.l{1} < Red.n{1} + Red.q{1});
  first by wp; skip; progress=> //;
           rewrite /Array.create empty_unique // ?init_length //.
inline Red(ADV).garble1 Red(ADV).garble2 RedAda(ADV,DKCS.Dkc).garble Red(ADV).get_challenge.
seq  5  5: (={glob ADV, glob DKCS.Dkc} /\
            Red.l{1} = RedAda.l{2} /\
            Red.query{1} = RedAda.query{2} /\
            Red.c{1} = RedAda.c{2} /\
            Red.fc{1} = RedAda.fc{2} /\
            Red.xc{1} = RedAda.xc{2} /\
            Red.n{1} = RedAda.n{2} /\
            Red.m{1} = RedAda.m{2} /\
            Red.q{1} = RedAda.q{2} /\
            Red.aa{1} = RedAda.aa{2} /\
            Red.bb{1} = RedAda.bb{2} /\
            Red.gg{1} = RedAda.gg{2} /\
            Red.pp{1} = RedAda.pp{2} /\
            Red.t{1} = RedAda.t{2} /\
            Red.v{1} = RedAda.v{2} /\
            Red.yy{1} = RedAda.yy{2} /\
            Red.xx{1} = RedAda.xx{2} /\
            Red.randG{1} = RedAda.randG{2} /\
            Red.tau{1} = RedAda.tau{2} /\
            Red.queries{1} = Array.empty /\
            Red.i{1} = RedAda.i{2} /\
            Red.v{1} = RedAda.v{2} /\
            Red.t{1} = RedAda.t{2} /\
            Red.g{1} = RedAda.g{2} /\
            length Red.v{1} = Red.n{1} + Red.q{1} /\
            length Red.t{1} = Red.n{1} + Red.q{1} /\
            0 <= Red.l{1} < Red.n{1} + Red.q{1}).
  wp; while (Red.i{1} = RedAda.i{2} /\
             Red.n{1} = RedAda.n{2} /\
             Red.q{1} = RedAda.q{2} /\
             Red.fc{1} = RedAda.fc{2} /\
             Red.xc{1} = RedAda.xc{2} /\
             length Red.v{1} = length RedAda.v{2} /\
             length Red.t{1} = length RedAda.t{2} /\
             length Red.v{1} = Red.n{1} + Red.q{1} /\
             length Red.t{1} = Red.n{1} + Red.q{1} /\
             (forall j, 0 <= j < Red.n{1} + Red.q{1} =>
               Red.v.[j]{1} = RedAda.v.[j]{2}) /\
             (forall j, 0 <= j < Red.n{1} + Red.q{1} =>
               Red.t.[j]{1} = RedAda.t.[j]{2})).
    wp; skip; progress=> //; first 4 smt.
      by case (j = RedAda.i){2}; [smt | intros=> neq; rewrite 2?set_get // /=; smt].
      by case (j = RedAda.i){2}; smt.
  while (Red.i{1} = RedAda.i{2} /\
         Red.n{1} = RedAda.n{2} /\
         Red.m{1} = RedAda.m{2} /\
         Red.q{1} = RedAda.q{2} /\
         Red.fc{1} = RedAda.fc{2} /\
         Red.xc{1} = RedAda.xc{2} /\
         length Red.v{1} = length RedAda.v{2} /\
         length Red.t{1} = length RedAda.t{2} /\
         length Red.v{1} = Red.n{1} + Red.q{1} /\
         length Red.t{1} = Red.n{1} + Red.q{1} /\
         (forall j, 0 <= j < Red.n{1} + Red.q{1} =>
           Red.v.[j]{1} = RedAda.v.[j]{2}) /\
         (forall j, 0 <= j < Red.n{1} + Red.q{1} =>
           Red.t.[j]{1} = RedAda.t.[j]{2})).
    wp; rnd; wp; skip; progress=> //; first 4 smt.
      by case (j = RedAda.i){2}; [smt | intros=> neq; rewrite 2?set_get // /=; smt].
      by case (j = RedAda.i){2}; smt.
  wp; skip; progress=> //.
    by rewrite H9.
    by rewrite H10.
    apply extensionality; rewrite /Array.(==); progress=> //.
      smt.
      by case (i0 = RedAda.l){2}; [smt | intros=> neq; rewrite 2?set_get // /=; smt].
    by apply extensionality; rewrite /Array.(==); progress=> //; smt.
    by apply extensionality; rewrite /Array.(==); progress=> //; smt.
    apply extensionality; rewrite /Array.(==); progress=> //.
      smt.
      by case (i0 = RedAda.l){2}; [smt | intros=> neq; rewrite 2?set_get // /=; smt].
    smt.

  (* Loop manipulation goes here *)

  (*right*)
  inline DKCS.Dkc.get_challenge.
  inline RedAda(ADV, DKCS.Dkc).garble.

  (*left*)
  inline DKCS.Game(DKCS.Dkc, Red(ADV)).work.
  inline Red(ADV).gen_queries.
  inline Red(ADV).get_challenge.
  inline Red(ADV).garble1.
  inline Red(ADV).garble2.


  admit.
qed.

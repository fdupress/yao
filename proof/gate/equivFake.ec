require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Real.
require import Bool.

require import Dkc.
require import Gate.
require import GarbleTools.
require import AdvGate.

axiom introTuple4 :
  forall (h:('a*'b*'c*'d), v:bool),
   (let (a, b, c, d) = h in v) = (forall a b c d, (a, b, c, d) = h => v).

module Fake(A:Gate.Adv) = {
  fun fake() : bool = {
    var c : bool;
    var query : Gate.query;
    var ret : Dkc.query list;
    var challenge : bool;
    var gg : Gate.functG;
    var query0 : Gate.funct*Gate.input;
    var query1 : Gate.funct*Gate.input;
    var v : bool;

    var rand : bool;
    var tau : bool;
    var t : bool;
    var keyt : token;
    var keynt : token;
    var keytau : token;
    var keyntau : token;
    var key_t_tau : token;
    var key_nt_ntau : token;
    var key_nt_tau : token;
    var key_t_ntau : token;

    var input : Gate.inputG;
    var g : ((bool*bool), token) map;

    (* t^^(fst xc) = t *)

    tau = $Dbool.dbool;
    keytau = $Dkc.genRandKeyLast(tau);

    query = A.gen_query();
    query0 = fst query;
    query1 = snd query;
    if (Gate.queryValid query)
    {
    v = Gate.eval (fst query0) (snd query0);
    
    t = $Dbool.dbool;

    keyt = $Dkc.genRandKeyLast(t);
    key_t_tau = $Dkc.genRandKey;

    keynt = $Dkc.genRandKeyLast(!t);
    key_nt_tau = $Dkc.genRandKey;

    key_t_ntau = $Dkc.genRandKeyLast(v);

    keyntau = $Dkc.genRandKeyLast(!tau);
    key_nt_ntau  = $Dkc.genRandKey;

    input = (keyt, keyntau);
    
    g.[( !tau,  t)] = Dkc.encode
      (tweak 2 (!tau) ( t))
      keyntau
      keyt
      key_t_ntau;
    g.[( !tau, !t)] = Dkc.encode
      (tweak 2 (!tau) (!t))
      keyntau
      keynt
      key_nt_ntau;
    g.[( tau,  t)] = Dkc.encode
      (tweak 2 ( tau) ( t))
      keytau
      keyt
      key_t_tau;
    g.[( tau,  !t)] = Dkc.encode
      (tweak 2 ( tau) (!t))
      keytau
      keynt
      key_nt_tau;

    gg = (proj g.[(false, false)], proj g.[(false, true)], proj g.[(true, false)], proj g.[(true, true)]);
    challenge = A.get_challenge((gg, input, tt));
    }
    else
      challenge = $Dbool.dbool;
    c = $Dbool.dbool;
    return (c = challenge) = false;
  }
}.


lemma fakePr :
  forall &m,
  forall (Adv <: Gate.Adv),
      Pr[Fake(Adv).fake()@ &m: !res] = 1%r / 2%r.
proof.
admit.
save.


lemma fakeEq :
  forall (ADV <: Gate.Adv {AdvGate.Adv, Fake, Dkc.Dkc}),
    equiv [
      Dkc.Game(Dkc.Dkc, Adv(ADV)).work ~ Fake(ADV).fake :
      (! Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=1 /\ (glob ADV){1} = (glob ADV){2}) ==> res{1} = res{2}
    ].
proof.
  intros ADV.
  fun.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGate.Adv(ADV).gen_queries.
  inline {1} AdvGate.Adv(ADV).get_challenge.
  inline {1} AdvGate.Adv(ADV).compute1.
  inline {1} AdvGate.Adv(ADV).gen_queries1.

  wp.
  swap {2} 7 -4. (* Move c *)
 
  app 11 6 : (
    info0{1} = tau{2} /\
    Dkc.Dkc.ksec{1} = keytau{2} /\
    fst query{1} = query0{1} /\
    snd query{1} = query1{1} /\
    fst query{2} = query0{2} /\
    snd query{2} = query1{2} /\
    query{1} = query{2} /\
    AdvGate.Adv.c{1} = c{2} /\
    Dkc.Dkc.b{1} = false /\
    Dkc.Dkc.r{1} = Map.empty /\
    Dkc.Dkc.kpub{1} = Map.empty /\
    AdvGate.Adv.l{1}=1
  );wp.
    call ((glob ADV){1} = (glob ADV){2}) (res{1} = res{2} /\ (glob ADV){1} = (glob ADV){2});[
      fun true;smt|
      wp;rnd;wp;rnd;rnd;skip;intros &1 &2;simplify;smt
    ].

  case (Gate.queryValid query{1}).

  (rcondt {1} 1;[intros &m;skip;smt|]). (* good *)
  (rcondt {2} 1;[intros &m;skip;smt|]). (* good *)

  (rcondf {1} 2;[intros &m;wp;skip;smt|]). (* l condition *)
  (rcondt {1} 2;[intros &m;wp;skip;smt|]). (* l condition *)
  (rcondt {1} 10;[intros &m;wp;rnd;rnd;wp;skip;intros &1 b c d e f;admit|]). (* While *)
  (rcondt {1} 16;[admit|]). (* While *)
  (rcondf {1} 22;[admit|]). (* While *)
 
  (rcondt {1} 23;[admit|]). (* good *)

  (rcondf {1} 23;[admit|]). (* l condition *)
  (rcondt {1} 23;[admit|]). (* l condition *)
  
  (call (answer{1}=answer{2}/\(glob ADV){1} = (glob ADV){2}) (res{1} = res{2});[fun true;smt|]). (* Call Adv get_challenge *)
  wp.
  rnd. (* key_nt_ntau *)
  rnd. (* keyntau *)
  wp.
  case ((Gate.eval AdvGate.Adv.fc{1} Adv.xc{1}) = (Gate.eval AdvGate.Adv.fc{1} (fst AdvGate.Adv.xc{1}, ! (snd AdvGate.Adv.xc{1})))).
  (rcondf {1} 26;[admit|]).
  rnd. (* key_t_ntau *)
  wp.

  (*BEGIN DKC*)
  (*LOOP 1*)
  (rcondt {1} 19;[admit|]). (* Dkc used *)
  wp.
  (rcondt {1} 20;[admit|]). (* Dkc not reusing *)
  (rcondf {1} 21;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 21;[admit|]). (* Dkc not reusing *)
  rnd. (* key_nt_tau *)
  rnd. (* keynt *)
  wp.
  (*LOOP 2*)
  (rcondt {1} 13;[admit|]). (* Dkc used *)
  wp.
  (rcondt {1} 14;[admit|]). (* Dkc not reusing *)
  (rcondf {1} 15;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 15;[admit|]). (* Dkc not reusing *)
  rnd. (* key_t_tau *)
  rnd. (* keyt *)
  wp.
  (*END DKC*)
  rnd {1}. (* rand *)
  rnd (lambda x, x^^(fst AdvGate.Adv.xc{1})) _. (* t *)
  wp.

  skip.
  progress.
  smt.
  smt.
  smt.
  smt.
  cut test : ((x1, x2, x3, x4) = ((0, tL ^^ fst Adv.xc{1}),
             (1, Gate.eval Adv.fc{1} (fst Adv.xc{1}, !(snd Adv.xc{1}))),
             false, tweak 0 (!(tL ^^ fst Adv.xc{1})) tau{2})).
  generalize H7.
  generalize ((0, tL ^^ fst Adv.xc{1}),
             (1, Gate.eval Adv.fc{1} (fst Adv.xc{1}, !(snd Adv.xc{1}))),
             false, tweak 0 (!(tL ^^ fst Adv.xc{1})) tau{2}).
  generalize ((0, !(tL ^^ fst Adv.xc{1})), (2, rand), false,
        tweak 0 (!(tL ^^ fst Adv.xc{1})) tau{2}).
  generalize (x1, x2, x3, x4).
intros x.
intros y.
intros z.
intros hhh.
  smt.
smt.
import Array.
smt.
  cut test : ((tL ^^ fst Adv.xc{1}) = snd x1).
  
  smt.

idtac.
  smt.
  admit.
  admit.
  smt.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  smt.
  smt.
  smt.

  intros &1 &2 pre.
  elim pre; clear pre; intros pre eqeval.
  elim pre; clear pre; intros pre tau.
  elim pre; clear pre; intros keytau pre.
  elim pre; clear pre; intros eqquery0L pre.
  elim pre; clear pre; intros eqquery1L pre.
  elim pre; clear pre; intros eqquery0R pre.
  elim pre; clear pre; intros eqquery1R pre.
  elim pre; clear pre; intros eqquery pre.
  elim pre; clear pre; intros eqc pre.
  elim pre; clear pre; intros bval pre.
  elim pre; clear pre; intros rval pre.
  elim pre; clear pre; intros kpubval lval.
  rewrite rval.
  rewrite kpubval.
  simplify.
  intros t1 t2.
  split;[cut lem : (forall (a b:bool), b ^^ a ^^ a = b);smt|].
  intros int eqt.
  intros rand inrand.
  simplify.
  elimT elim_p 


    intros keyt1 keyt2;(split;[smt|]);intros eqkeyt inkeyt;
    intros key_t_tau inkey_t_tau.

    (* UGLY *)
    rewrite (tl_def<:(int*bool)*(int*bool)*bool*(bool array)> ((0, t1 ^^ fst (snd (fst query{1}))),
    (1,
      eval (fst (fst query{1})) (fst (snd (fst query{1})),
        !snd (snd (fst query{1})))),
      false, tweak 0 (!t1 ^^ (fst (snd (fst query{1})))) AdvGate.Adv.tau{1})
(
    (((0, !t1 ^^ fst (snd (fst query{1}))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1}) ::
      __nil)));
    rewrite (hd_def<:(int*bool)*(int*bool)*bool*(bool array)>
    ((0, !t1 ^^ fst (snd (fst query{1}))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1}) __nil);
    rewrite (tl_def<:(int*bool)*(int*bool)*bool*(bool array)> ((0, t1 ^^ fst (snd (snd query{1}))),
    (1,
      eval (fst (snd query{1})) (fst (snd (snd query{1})),
        !snd (snd (snd query{1})))),
      false, tweak 0 (!t1 ^^ (fst (snd (snd query{1})))) AdvGate.Adv.tau{1})
(
    (((0, !t1 ^^ fst (snd (snd query{1}))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1}) ::
      __nil)));
    rewrite (hd_def<:(int*bool)*(int*bool)*bool*(bool array)>
    ((0, !t1 ^^ fst (snd (snd query{1}))),
      (2, rand), false, tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1}) __nil);
    (* END UGLY *)

    (rewrite (_:Dkc.Dkc.b{1} = false);[smt|]);
    simplify;
    intros keynt1 keynt2; (split;[smt|]);intros eqkeynt inkeynt;
    intros key_nt_tau inkey_nt_tau;

    (* UGLY *)

rewrite (hd_def<:Dkc.key*Dkc.key*Dkc.cipher>
(proj Map.empty.[(0,
    t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
    !t1 ^^ fst (snd (fst query{1}))) <- keynt1].[(0,
    !t1 ^^ fst (snd (fst query{1})))],

    proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
      !t1 ^^ fst (snd (fst query{1}))) <- keynt1].[(2, rand)],

      Dkc.encode
        (tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1})
        (proj Map.empty
          .[(0,t1 ^^ fst (snd (fst query{1}))) <- keyt1]
          .[(0,!t1 ^^ fst (snd (fst query{1}))) <- keynt1]
          .[(0,!t1 ^^ fst (snd (fst query{1})))]) 
        Dkc.Dkc.ksec{1}
        (proj Map.empty.[(1, eval (fst (fst query{1})) (fst (snd (fst query{1})),
          !snd (snd (fst query{1})))) <- key_t_tau]
        .[(2, rand) <- key_nt_tau]
        .[(2, rand)])
)

(

(proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
      t1 ^^ fst (snd (fst query{1})))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(1,
        eval (fst (fst query{1})) (fst (snd (fst query{1})),
          !snd (snd (fst query{1}))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1}) (proj Map.empty.[(0,
          t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
          t1 ^^ fst (snd (fst query{1})))]) Dkc.Dkc.ksec{1} (proj Map.empty.[(1,
          eval (fst (fst query{1})) (fst (snd (fst query{1})),
            !snd (snd (fst query{1})))) <- key_t_tau].[(1,
          eval (fst (fst query{1})) (fst (snd (fst query{1})),
            !snd (snd (fst query{1}))))])) ::
      __nil));


rewrite (hd_def<:Dkc.key*Dkc.key*Dkc.cipher>
(proj Map.empty.[(0,
    t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
    !t1 ^^ fst (snd (snd query{1}))) <- keynt1].[(0,
    !t1 ^^ fst (snd (snd query{1})))],

    proj Map.empty.[(0,
      t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
      !t1 ^^ fst (snd (snd query{1}))) <- keynt1].[(2, rand)],

      Dkc.encode
        (tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1})
        (proj Map.empty
          .[(0,t1 ^^ fst (snd (snd query{1}))) <- keyt1]
          .[(0,!t1 ^^ fst (snd (snd query{1}))) <- keynt1]
          .[(0,!t1 ^^ fst (snd (snd query{1})))]) 
        Dkc.Dkc.ksec{1}
        (proj Map.empty.[(1, eval (fst (snd query{1})) (fst (snd (snd query{1})),
          !snd (snd (snd query{1})))) <- key_t_tau]
        .[(2, rand) <- key_nt_tau]
        .[(2, rand)])
)

(

(proj Map.empty.[(0,
      t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
      t1 ^^ fst (snd (snd query{1})))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(1,
        eval (fst (snd query{1})) (fst (snd (snd query{1})),
          !snd (snd (snd query{1}))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1}) (proj Map.empty.[(0,
          t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
          t1 ^^ fst (snd (snd query{1})))]) Dkc.Dkc.ksec{1} (proj Map.empty.[(1,
          eval (fst (snd query{1})) (fst (snd (snd query{1})),
            !snd (snd (snd query{1})))) <- key_t_tau].[(1,
          eval (fst (snd query{1})) (fst (snd (snd query{1})),
            !snd (snd (snd query{1}))))])) ::
      __nil));
    (* END UGLY *)
    simplify;
    (* UGLY *)

rewrite (tl_def<:Dkc.key*Dkc.key*Dkc.cipher>
(proj Map.empty.[(0,
    t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
    !t1 ^^ fst (snd (fst query{1}))) <- keynt1].[(0,
    !t1 ^^ fst (snd (fst query{1})))],

    proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
      !t1 ^^ fst (snd (fst query{1}))) <- keynt1].[(2, rand)],

      Dkc.encode
        (tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1})
        (proj Map.empty
          .[(0,t1 ^^ fst (snd (fst query{1}))) <- keyt1]
          .[(0,!t1 ^^ fst (snd (fst query{1}))) <- keynt1]
          .[(0,!t1 ^^ fst (snd (fst query{1})))]) 
        Dkc.Dkc.ksec{1}
        (proj Map.empty.[(1, eval (fst (fst query{1})) (fst (snd (fst query{1})),
          !snd (snd (fst query{1})))) <- key_t_tau]
        .[(2, rand) <- key_nt_tau]
        .[(2, rand)])
)

(

(proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
      t1 ^^ fst (snd (fst query{1})))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(1,
        eval (fst (fst query{1})) (fst (snd (fst query{1})),
          !snd (snd (fst query{1}))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1}) (proj Map.empty.[(0,
          t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
          t1 ^^ fst (snd (fst query{1})))]) Dkc.Dkc.ksec{1} (proj Map.empty.[(1,
          eval (fst (fst query{1})) (fst (snd (fst query{1})),
            !snd (snd (fst query{1})))) <- key_t_tau].[(1,
          eval (fst (fst query{1})) (fst (snd (fst query{1})),
            !snd (snd (fst query{1}))))])) ::
      __nil));
rewrite (hd_def<:Dkc.key*Dkc.key*Dkc.cipher>

(proj Map.empty.[(0,
      t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
      t1 ^^ fst (snd (fst query{1})))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(1,
        eval (fst (fst query{1})) (fst (snd (fst query{1})),
          !snd (snd (fst query{1}))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (fst query{1}))) AdvGate.Adv.tau{1}) (proj Map.empty.[(0,
          t1 ^^ fst (snd (fst query{1}))) <- keyt1].[(0,
          t1 ^^ fst (snd (fst query{1})))]) Dkc.Dkc.ksec{1} (proj Map.empty.[(1,
          eval (fst (fst query{1})) (fst (snd (fst query{1})),
            !snd (snd (fst query{1})))) <- key_t_tau].[(1,
          eval (fst (fst query{1})) (fst (snd (fst query{1})),
            !snd (snd (fst query{1}))))])) 
      __nil);






rewrite (tl_def<:Dkc.key*Dkc.key*Dkc.cipher>
(proj Map.empty.[(0,
    t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
    !t1 ^^ fst (snd (snd query{1}))) <- keynt1].[(0,
    !t1 ^^ fst (snd (snd query{1})))],

    proj Map.empty.[(0,
      t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
      !t1 ^^ fst (snd (snd query{1}))) <- keynt1].[(2, rand)],

      Dkc.encode
        (tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1})
        (proj Map.empty
          .[(0,t1 ^^ fst (snd (snd query{1}))) <- keyt1]
          .[(0,!t1 ^^ fst (snd (snd query{1}))) <- keynt1]
          .[(0,!t1 ^^ fst (snd (snd query{1})))]) 
        Dkc.Dkc.ksec{1}
        (proj Map.empty.[(1, eval (fst (snd query{1})) (fst (snd (snd query{1})),
          !snd (snd (snd query{1})))) <- key_t_tau]
        .[(2, rand) <- key_nt_tau]
        .[(2, rand)])
)

(

(proj Map.empty.[(0,
      t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
      t1 ^^ fst (snd (snd query{1})))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(1,
        eval (fst (snd query{1})) (fst (snd (snd query{1})),
          !snd (snd (snd query{1}))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1}) (proj Map.empty.[(0,
          t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
          t1 ^^ fst (snd (snd query{1})))]) Dkc.Dkc.ksec{1} (proj Map.empty.[(1,
          eval (fst (snd query{1})) (fst (snd (snd query{1})),
            !snd (snd (snd query{1})))) <- key_t_tau].[(1,
          eval (fst (snd query{1})) (fst (snd (snd query{1})),
            !snd (snd (snd query{1}))))])) ::
      __nil));
rewrite (hd_def<:Dkc.key*Dkc.key*Dkc.cipher>

(proj Map.empty.[(0,
      t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
      t1 ^^ fst (snd (snd query{1})))],

      proj Map.empty.[(0,
        t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(1,
        eval (fst (snd query{1})) (fst (snd (snd query{1})),
          !snd (snd (snd query{1}))))],

        Dkc.encode (tweak 0 (!t1 ^^ fst (snd (snd query{1}))) AdvGate.Adv.tau{1}) (proj Map.empty.[(0,
          t1 ^^ fst (snd (snd query{1}))) <- keyt1].[(0,
          t1 ^^ fst (snd (snd query{1})))]) Dkc.Dkc.ksec{1} (proj Map.empty.[(1,
          eval (fst (snd query{1})) (fst (snd (snd query{1})),
            !snd (snd (snd query{1})))) <- key_t_tau].[(1,
          eval (fst (snd query{1})) (fst (snd (snd query{1})),
            !snd (snd (snd query{1}))))])) 
      __nil);
    (* END UGLY *)

simplify;

    intros key_t_ntau1 key_t_ntau2;(split;[(*smt*)admit|]);intros eqkey_t_ntau inkey_t_ntau;
    intros key_ntau1 key_ntau2;(split;[smt|]);intros eqkey_ntau inkey_ntau;
    intros key_nt_ntau inkey_nt_ntau;
    (split;[admit(*TODO*)|]);
    intros h;
    clear h;
    smt.

(*case else : BAD*)
  (rcondf {1} 1;[intros &m;skip;smt|]).
  (rcondf {1} 7;[intros &m;wp;skip;smt|]).
  (rcondf {1} 9;[intros &m;wp;skip;smt|]).
  (rcondf {2} 1;[intros &m;wp;skip;smt|]).
  rnd.
  wp.
  skip.
  intros _ _ _.
  simplify.
  smt.
save.

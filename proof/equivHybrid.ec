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
require AdvGate.

lemma hybridEq :
      forall (Adv <: Gate.Adv),
        equiv [
          Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work ~
            Dkc.Game(Dkc.Dkc, AdvGate.Adv(Adv)).work :
          (!Dkc.Dkc.b{1}) /\ (AdvGate.Adv.l{1}=0) /\
          (Dkc.Dkc.b{2}) /\ (AdvGate.Adv.l{2}=1)
          ==> !res{1} = res{2}
        ]
proof.
  intros Adv.
  fun.
  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGate.Adv(Adv).gen_queries.
  inline {1} AdvGate.Adv(Adv).get_challenge.
  inline {1} AdvGate.Adv(Adv).compute0.
  inline {1} AdvGate.Adv(Adv).gen_queries0.
  inline {2} Dkc.Dkc.preInit.
  inline {2} Dkc.Dkc.get_challenge.
  inline {2} Dkc.Dkc.initialize.
  inline {2} Dkc.Dkc.encrypt.
  inline {2} AdvGate.Adv(Adv).gen_queries.
  inline {2} AdvGate.Adv(Adv).get_challenge.
  inline {2} AdvGate.Adv(Adv).compute1.
  inline {2} AdvGate.Adv(Adv).gen_queries1.
 
  swap [7..9] -6.

  app 3 3 : (
    AdvGate.Adv.c{1} = AdvGate.Adv.c{2} /\
    AdvGate.Adv.fc{1} = AdvGate.Adv.fc{2} /\
    AdvGate.Adv.xc{1} = AdvGate.Adv.xc{2} /\
    query{1} = query{2} /\
    AdvGate.Adv.l{1}=0 /\
    Dkc.Dkc.b{1} = false /\
    AdvGate.Adv.l{2}=1 /\
    Dkc.Dkc.b{2} = true
  ).
wp. call true (res{1}=res{2}).
admit.
rnd.
skip.
simplify.
intros &1 &2 h.
intros x hypx. split. trivial.
intros hypx2 hypx3.
intros L R hypLR.
simplify.
trivial.
[admit|rnd;skip;trivial]|]. (* Call adv gen_queries *)

  case (Gate.eval (fst (fst query{2})) (snd (fst query{2})) = Gate.eval (fst (snd query{2})) (snd (snd query{2}))). (*good*)

  rcondt {1} 9;[intros &m;wp;rnd;wp;rnd;skip;trivial|]. (*good*)
  rcondf {1} 11;[admit|]. (* l condition *)
  rcondt {1} 10;[admit|]. (* l condition *)
  rcondt {1} 17;[admit|]. (* While *)
  rcondt {1} 24;[admit|]. (* While *)
  rcondf {1} 31;[admit|]. (* While *)
  rcondt {1} 33;[admit|]. (* good *)
  rcondf {1} 34;[admit|]. (* l *)
  rcondt {1} 33;[admit|]. (* l *)

  rcondt {2} 9;[intros &m;wp;rnd;wp;rnd;skip;trivial|]. (*good*)
  rcondf {2} 10;[admit|]. (* l condition *)
  rcondt {2} 10;[admit|]. (* l condition *)
  rcondt {2} 18;[admit|]. (* While *)
  rcondt {2} 25;[admit|]. (* While *)
  rcondf {2} 32;[admit|]. (* While *)
  rcondt {2} 34;[admit|]. (* good *)
  rcondf {2} 34;[admit|]. (* l *)
  rcondt {2} 34;[admit|]. (* l *)

  wp.
  call (answer{1}=answer{2}) (res{1} = res{2});[admit|].
  wp.
  swap{1} [5..6] -3. (*rewrite tau*)
  swap{1} 9 -5. (*rewrite tau*)
  swap{1} 10 -5. (*t*)
  swap{1} 38 -32. (*keyntau*)

  swap{2} 10 -9. (*t*)
  swap{1} [6..7] -2. (*rewrite tau*)
  swap{1} 10 -5. (*rewrite tau*)
  swap{2} 39 -30. (*key_nt_ntau*)
  swap{2} 39 -25. (*keyntau*)
  swap{1} 38 -25. (*keyntau*)
  swap{1} 10 -8. (*t*)
  swap{2} 11 -10. (*t*)

  case (
(Gate.eval AdvGate.Adv.fc{1} AdvGate.Adv.xc{1}=Gate.eval AdvGate.Adv.fc{1} (!(fst AdvGate.Adv.xc{1}), (snd AdvGate.Adv.xc{1}))) /\
(Gate.eval AdvGate.Adv.fc{2} AdvGate.Adv.xc{2}=Gate.eval AdvGate.Adv.fc{2} (!(fst AdvGate.Adv.xc{2}), (snd AdvGate.Adv.xc{2})))
).
  rcondt{1} 37;[admit|].
  rcondt{1} 38;[admit|].
  rcondt{2} 39;[admit|].
  wp.

  (*BEGIN CLEAN DKC*)
  (*LOOP 2*)
  (rcondt {1} 28;[admit|]). (* Dkc used *)
  (rcondt {1} 29;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 30;[admit|]). (* Dkc not reusing *) (*TODO: FALSE*)
  (rcondt {1} 31;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 30;[admit|]). (* Dkc used *)
  (rcondt {2} 31;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 32;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 33;[admit|]). (* Dkc not reusing *)
  (*LOOP 1*)
  (rcondt {1} 21;[admit|]). (* Dkc used *)
  (rcondt {1} 22;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 23;[admit|]). (* Dkc not reusing *)
  (rcondt {1} 24;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 23;[admit|]). (* Dkc used *)
  (rcondt {2} 24;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 25;[admit|]). (* Dkc not reusing *)
  (rcondt {2} 26;[admit|]). (* Dkc not reusing *)
  (*END CLEAN DKC*)

  wp.

  rnd.
  rnd.
  swap{2} 37 -34.

OLD STUFF :










  rcondt {1} 11;[intros &m;wp;rnd;wp;rnd;rnd;skip;trivial|].
  rcondt {2} 11;[intros &m;wp;rnd;wp;rnd;rnd;skip;trivial|].


[intros &m;*(wp;try rnd;wp;try (call true true;admit);wp;try (skip;trivial))|]);



  inline {1} Dkc.Dkc.preInit.
  inline {1} Dkc.Dkc.get_challenge.
  inline {1} Dkc.Dkc.initialize.
  inline {1} Dkc.Dkc.encrypt.
  inline {1} AdvGate.Adv.gen_queries.
  inline {1} AdvGate.Adv.get_challenge.
  rcondt {1} 8;[admit|].
  rcondf {1} 9;[admit|].
  rcondt {1} 16;[admit|].
  rcondf {1} 17;[admit|].
  inline {1} AdvGate.Adv.compute0.
  inline {1} AdvGate.Adv.gen_queries0.

  inline {2} Dkc.Dkc.preInit.
  inline {2} Dkc.Dkc.get_challenge.
  inline {2} Dkc.Dkc.initialize.
  inline {2} Dkc.Dkc.encrypt.
  inline {2} AdvGate.Adv.gen_queries.
  inline {2} AdvGate.Adv.get_challenge.
  rcondf {2} 8;[admit|].
  rcondt {2} 8;[admit|].
  rcondf {2} 16;[admit|].
  rcondt {2} 16;[admit|].
  inline {2} AdvGate.Adv.compute1.
  inline {2} AdvGate.Adv.gen_queries1.

  wp.

  call true true.

  call (AdvGate.Adv.l{1}=0/\AdvGate.Adv.l{2}=1) (res{1}=res{2}).
    fun.
    call (answer{1}=answer{2}) (res{1}=res{2});[admit(*ADV rule*)|].
    wp.
    app 1 2 : (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\AdvGate.Adv.g{1}=AdvGate.Adv.g{2}/\AdvGate.Adv.l{1}=0/\AdvGate.Adv.l{2}=1).
    rcondf {2} 1;[intros &m;skip;trivial|].
    rcondt {1} 1;[intros &m;skip;trivial|].
    rcondt {2} 1;[intros &m;skip;trivial|].
    call (true) (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\AdvGate.Adv.g{1}=AdvGate.Adv.g{2}).


cut intro : (
          let preG_1 = AdvGate.Adv.preG{m1} in
          let preG_2 = AdvGate.Adv.preG{m2} in
          let g_1 = AdvGate.Adv.g{m1} in
          let g_2 = AdvGate.Adv.g{m2} in
          let fc = AdvGate.Adv.fc{m2} in
          let tau = AdvGate.Adv.tau{m2} in
          let x = AdvGate.Adv.x{m2} in
          let vis1 = (AdvGate.get AdvGate.Adv.xc{m2} 0)^^(proj AdvGate.Adv.t{m2}.[0]) in
equiv [AdvGate.Adv(Adv).computeG1 ~ AdvGate.Adv(Adv).computeG2 : (*&t1=&1/\&t2=&2*) true ==> AdvGate.Adv.input {1} =
  AdvGate.Adv.input {2} /\
  AdvGate.Adv.g {1} = AdvGate.Adv.g {2}]
);[|apply intro].
      
      intros preG1 preG2 g_1 g_2 fc tau x vis1.
      fun.
      wp.
      call (AdvGate.Adv.fc{1}=AdvGate.Adv.fc{2}/\AdvGate.Adv.xc{1}=AdvGate.Adv.xc{2}/\
        AdvGate.Adv.x{1}=AdvGate.Adv.x{2}/\ AdvGate.Adv.t{1}=AdvGate.Adv.t{2}/\
        AdvGate.Adv.g{1}=AdvGate.Adv.g{2}/\AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\(          if vis1 = tau then
            forall b, proj preG1.[(!vis1, b)] = proj preG2.[(!vis1, b)]
          else
            proj preG1.[(vis1, !tau)] = proj preG2.[(!vis1, !tau)])
        )
        (AdvGate.Adv.input{1}=AdvGate.Adv.input{2}/\(
          if vis1 = tau then
            (forall b, proj g_1.[(!vis1, b)] = proj g_2.[(!vis1, b)]) /\
            proj g_1.[(vis1,   !tau)] = AdvGate.enc x preG1 fc vis1 (!tau)
          else
            proj g_1.[(vis1, !tau)] = proj g_2.[(!vis1, !tau)] /\
            proj g_1.[(vis1,  tau)] = AdvGate.enc x preG1 fc vis1 tau /\
            proj g_2.[(tau,  true)] = AdvGate.enc x preG2 fc tau true /\
            proj g_2.[(tau,  false)] = AdvGate.enc x preG2 fc tau false
        )).
  (*
          let g_1 = AdvGate.Adv.g{2} in
          let g_2 = AdvGate.Adv.g{2} in
          let tau = AdvGate.Adv.tau{2} in
          let xc = AdvGate.Adv.xc{2} in
          let x = AdvGate.Adv.x{2} in
          let t = AdvGate.Adv.t{2} in
          let x1 = get xc 0 in
          let x2 = get xc 1 in
          let t2 = proj t.[1] in
          let val0 = Gate.eval fc (!x1, false) in
          let val1 = Gate.eval fc (!x1, true) in
          let vis1 = x1^^(proj t.[0]) in
 *)
        fun.
        wp.
        skip.
        intros &1 &2 h.
        split.
        trivial.

        elim h; clear h; intros h1 h;
        elim h; clear h; intros h2 h;
        elim h; clear h; intros h3 h;
        elim h; clear h; intros h4 h;
        elim h; clear h; intros h5 h;
        elim h; clear h; intros h6.

        cut lem1 : (forall b1 b2, proj (Map.__get g_1 (b1, b2)) = AdvGate.enc AdvGate.Adv.x{1} preG1 AdvGate.Adv.fc{1} b1 b2). (*TODO*) admit.
        cut lem2 : (forall b1 b2, proj (Map.__get g_2 (b1, b2)) = AdvGate.enc AdvGate.Adv.x{2} preG1 AdvGate.Adv.fc{2} b1 b2). (*TODO*) admit.

        case (vis1 = tau).
        intros hvt h.



        split.
        intros b.
        rewrite (lem1 (!vis1) b).
        rewrite (lem2 (!vis1) b).
        delta AdvGate.enc.
        simplify.
        rewrite (_ : proj preG1.[(!vis1,  b)] = proj preG2.[(!vis1, b)]);[apply (h b)|trivial].
        rewrite (lem1 vis1 (!tau)).
        rewrite h1.
        rewrite h3.
        delta x fc.
        trivial.


          admit. (*TODO:*)
        split.
          admit. (*TODO:*)
        admit.
        intros hvt.
        split.
          admit. (*TODO:*)
        split.
          admit. (*TODO:*)
        admit.
      intros _ _.
        
        trivial.
      intros _ _.
      app 11 8 : true.
        call true true.
        fun.
        call true true.
        fun.
        wp.
    intros _ _.
    rcondf {1} 1;[intros &m;skip;trivial|].
    rcondf {1} 1;[intros &m;skip;trivial|].
    rcondf {2} 1;[intros &m;skip;trivial|].
    skip.
    intros &1 &2 h.
    split.
    cut lem : (forall b1 b2,
      proj AdvGate.Adv.g{1}.[(b1, b2)] = proj AdvGate.Adv.g{1}.[(b1, b2)]).
    trivial.
    trivial.
    trivial.

call
  ((!Dkc.Dkc.b{1} = Dkc.Dkc.b{2}))
  (!res{1} = res{2}).
  fun.
  skip.
  trivial.
intros resultDkc_L resultDkc_R.
while (true).
  wp.
  call (true) (res{1} = res{2}).
    admit.
  admit.
  wp.
  app 1 1 : (true).
    call (true) (true).
      fun.
      rnd.
      skip.
      trivial.
    intros result_L0 result_R0.
    skip.
    trivial.
    admit. (*Call adv*)
admit. (*
call
  (true)
  (res{1} = res{2}).
  fun.
  skip.
  trivial.*)
save.
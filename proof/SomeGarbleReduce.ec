require import Real.
require import Int.
require import IntDiv.
require import FSet.
require import NewFMap.
require import Array.
require import Distr.
require import Bool.
require import Pair.
require import DInterval.
require import Option.

require (*--*) DKC.
require (*--*) DKCSec2.

require import GarbleTools.
  
require import ArrayExt.

import ForLoop.

require import SomeGarble.

import GSch.Sch.
import W.
import SomeGarble.DKCSecurity.
import SomeGarble.Tweak.

(** 'l' parameter and its position *)
op l : int.
axiom l_pos : 0 <= l < SomeGarble.bound.

module AdvRandomInit (D : DKC_t) = {
  proc init(useVisible:bool, lsb:bool): unit = {
    var v, trnd, i;

    R.t = offun (fun x, false) (C.n + C.q);
    R.xx = map0;
    
    i = 0;
    while (i < C.n + C.q) {
      trnd = ${0,1};
      v = if useVisible then C.v.[i] else false;
      trnd = if (i < C.n + C.q - C.m) then trnd else v;
      
      R.t.[i] = trnd;
      
      i = i + 1;
    }

    R.t.[l] = !lsb;
  }
}.

module AdvInit (D : DKC_t) = {

  proc query_garble_dummy (alpha : bool, betha : bool) : unit = {
    var twe : word;
    var gamma, pos : bool;
    var i,j : int;
    var ki, kj, zz,r : word;
    
    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ betha);
    gamma = C.v.[G.g] ^^ oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ betha)];
    
    (ki,kj,zz) = D.encrypt(true, (G.a, R.t.[G.a] ^^ alpha), (G.b, R.t.[G.b] ^^ betha), (C.n+C.q, R.t.[G.g]), twe);
    
    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ betha)] = zz;
  }
  
  proc query_garble (alpha : bool, betha : bool) : unit = {
    var twe : word;
    var gamma, pos : bool;
    var i,j : int;
    var ki, kj, zz : word;
    
    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ betha);
    gamma = C.v.[G.g] ^^ oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ betha)];
    
    (ki,kj,zz) = D.encrypt(false, (G.a, R.t.[G.a] ^^ alpha), (G.b, R.t.[G.b] ^^ betha), (G.g, R.t.[G.g] ^^ gamma), twe);
    
    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ betha)] = zz;
  }
  
  proc init() : unit = {
    var tok, yy : word;

    G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
    G.pp = map0;
    G.randG = map0;
    G.a = 0;
    G.b = 0;
      
    G.g = C.n;
    while (G.g < C.n + C.q) {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];

      if (!(G.a < l)) {
         query_garble(false, false);
         query_garble(true, false);
         query_garble(false, true);
         query_garble(true, true);
      }

      else {
        if ((G.a < l) /\ !(G.b < l)) {
          query_garble(false, false);
          query_garble_dummy(true,false);
          query_garble(false,true);
          query_garble_dummy(true,true);
        }

         else {
          (*cifrar random*)
          query_garble(false, false);
          query_garble_dummy(true,false);
          query_garble_dummy(false,true);
          query_garble_dummy(true,true);
        }
      }
      
      G.g = G.g + 1;
    }
  }
}.

module DKC_Adv (D : DKC_t, Adv_IND : GSch.EncSecurity.Adv_IND_t) : Adv_DKC_t = {

  proc get_challenge (lsb:bool) : bool = {
    var query_ind : GSch.EncSecurity.query_IND;
    var p : GSch.EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query_ind = Adv_IND.gen_query();
      
    if (GSch.EncSecurity.queryValid_IND query_ind) {
      real = ${0,1};
      p = if real then snd query_ind else fst query_ind;
      CircuitInit.init(p);
      AdvRandomInit(D).init(true, lsb);
      AdvInit(D).init();
        
      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
          
      adv = Adv_IND.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

require import SomeGarbleHy.

lemma GameHybrid_l1_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = l /\ DKCSecurity.boundl = SomeGarble.bound /\ l{1} = l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} ==> ={res}].
proof.  
  move => Agen_ll Aget_ll.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  swap{2} 11 -10.
  seq 1 1 : (={glob A} /\ query{1} = query_ind{2} /\
    (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\
    DKCSecurity.l = Top.l /\ DKCSecurity.boundl = SomeGarble.bound /\
    l{1} = Top.l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2}); first by call (_ : true).

  case (GSch.EncSecurity.queryValid_IND query{1}).
    rcondt{1} 1; first by progress.
    rcondt{2} 11; first by auto; (while (true); first by auto); auto. 
    swap{2} 11 -10.
    swap{2} 12 -10.
    swap{2} 13 -10.
    seq 3 3 : ((={glob A,real,p} /\
      query{1} = query_ind{2} /\ 
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\ DKCSecurity.boundl = SomeGarble.bound /\
      l{1} = Top.l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2}) /\
      GSch.EncSecurity.queryValid_IND query{1} /\ ={glob C} /\
      size C.v{1} = (C.n + C.q){1} /\
      C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
      validInputsP (C.f, C.x){1} /\
      (forall i, 0 <= i < C.n{2} => C.v{2}.[i] = C.x{2}.[i]) /\
      (forall i, C.n <= i < C.n + C.q => C.v{2}.[i] = oget C.gg.[(i, C.v{2}.[C.aa{2}.[i]], C.v{2}.[C.bb.[i]])]){2}).
      call CircuitInitEquiv.
      auto; progress. 
        by move : H4; rewrite /queryValid_IND /valid_plain /validInputs /validInputsP ?valid_wireinput /valid_circuitP /fst /snd; case realL => /#. 
        simplify validBound; case realL => /#.

    seq 1 11 : (={glob A, real, p} /\
      query{1} = query_ind{2} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\ 
      l{1} = Top.l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\
      GSch.EncSecurity.queryValid_IND query{1} /\
      ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
      size C.v{1} = C.n{1} + C.q{1} /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
      (forall (i0 : int), 0 <= i0 < C.n{2} => C.v{2}.[i0] = C.x{2}.[i0]) /\
      (forall (i0 : int),
        C.n{2} <= i0 < C.n{2} + C.q{2} =>
        C.v{2}.[i0] =
        oget C.gg{2}.[(i0, C.v{2}.[C.aa{2}.[i0]], C.v{2}.[C.bb{2}.[i0]])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
      R.t{2}.[l] = !DKCp.lsb{2} /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
      oget R.xx{1}.[(l, !C.v{1}.[l])] = DKCp.ksec{2}).
    
      inline RandomInit.init AdvRandomInit(DKC).init.

      transitivity{2} {
        DKCp.lsb = witness;
        DKCp.ksec = witness;
        DKCp.used = fset0;
        DKCp.kpub = map0;
        i = 0;
        while (i < C.n + C.q) {
          if (i = l) {
            DKCp.lsb = ${0,1};
            DKCp.ksec = $Dword.dwordLsb (DKCp.lsb);
            DKCp.kpub.[(i,DKCp.lsb)] = witness;
            DKCp.kpub.[(i,!DKCp.lsb)] = $Dword.dwordLsb (!DKCp.lsb); (* can never return or encrypt this key *)
          }
          else {
            tok1 = $Dword.dwordLsb (false);
            tok2 = $Dword.dwordLsb (true);
            DKCp.kpub.[(i, false)] = tok1;
            DKCp.kpub.[(i, true)] = tok2;
          }
          i = i + 1;
        }
        useVisible = true;
        R.t = offun (fun (_ : int) => false) (C.n + C.q);
        i = 0;
        while (i < C.n + C.q) {
          trnd =$ {0,1};
          v = if useVisible then C.v.[i] else false;
          trnd = if i < C.n + C.q - C.m then trnd else v;
          R.t.[i] = trnd;
          i = i + 1;
        }
        R.t.[l] = !DKCp.lsb;
      }
      ( (={glob A, real, p} /\
          query{1} = query_ind{2} /\
        DKCSecurity.bound = C.n{1} + C.q{1} /\
        DKCSecurity.l = Top.l /\ 
          l{1} = Top.l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2}) /\
        GSch.EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
        (forall (i1 : int),
          C.n{2} <= i1 < C.n{2} + C.q{2} =>
          C.v{2}.[i1] =
          oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])])

        ==>

        ={glob A, real, p} /\
        query{1} = query_ind{2} /\
          DKCSecurity.bound = C.n{1} + C.q{1} /\
          DKCSecurity.l = Top.l /\
        l{1} = Top.l-1 /\ 
          DKCp.b{2} /\
          b{2} /\
          DKCp.b{2} = b{2} /\
        GSch.EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
        R.t{1}.[l] = !DKCp.lsb{2} /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
        oget R.xx{1}.[(l, !C.v{1}.[l])] = DKCp.ksec{2}
      )
      
      ( (={glob A, real, p, DKCp.b, b, query_ind} /\
          query_ind{1} = query_ind{2} /\
        DKCSecurity.bound = C.n{1} + C.q{1} /\
        DKCSecurity.l = Top.l /\ 
          DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2}) /\
        GSch.EncSecurity.queryValid_IND query_ind{1} /\
        ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
        (forall (i1 : int),
          C.n{2} <= i1 < C.n{2} + C.q{2} =>
          C.v{2}.[i1] =
          oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])])

        ==> 

        ={glob A, real, p, R.t, DKCp.b, DKCp.kpub, b, DKCp.lsb, DKCp.ksec, query_ind} /\
          DKCSecurity.bound = C.n{1} + C.q{1} /\
          DKCSecurity.l = Top.l /\
         i{1} = i0{2} /\
          DKCp.b{2} /\
          b{2} /\ i{1} = i0{2} /\ 
          DKCp.b{2} = b{2} /\ DKCSecurity.boundl = SomeGarble.bound /\
        GSch.EncSecurity.queryValid_IND query_ind{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        R.t{2}.[l] = !DKCp.lsb{2})
          .

          progress. exists (glob A){2}. exists C.aa{2}. exists C.bb{2}. exists (((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2})). exists (C.gg{2}). exists C.m{2}. exists C.n{2}.  exists C.q{2}. exists C.v{2}. exists (C.x{2}).      exists (b{2}). exists (b{2}). exists (p{2}). exists (query_ind{2}).  exists (real{2}). by progress. by progress. 

      swap{2} 7 -4. swap{2} 8 -5. fusion{2} 8!1 @ 1,4.
      
      wp.
      
  while (={glob A, real, p, i} /\
    query{1} = query_ind{2} /\ ={useVisible} /\ useVisible{2} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
    l{1} = Top.l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\
      GSch.EncSecurity.queryValid_IND query{1} /\ size R.t{1} = C.n{1} + C.q{1} /\
    ={glob C} /\ size R.t{1} = size R.t{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
      size C.v{1} = C.n{1} + C.q{1} /\ DKCSecurity.boundl = SomeGarble.bound /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
    (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
    (forall (i1 : int),
      C.n{2} <= i1 < C.n{2} + C.q{2} =>
      C.v{2}.[i1] =
      oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
    (forall k, 0 <= k < i{1} => k <> l => R.t{1}.[k] = R.t{2}.[k]) /\
    (forall k, 0 <= k < i{1} => k = l => R.t{1}.[k] = !DKCp.lsb{2}) /\
    (forall k, 0 <= k < i{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k = l => oget R.xx{1}.[(k,!C.v{1}.[k])] = DKCp.ksec{2})).
  
    if{2}; last first.

  case ((i < C.n + C.q - C.m){1}).
    swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\
     DKCSecurity.bound = C.n{1} + C.q{1} /\
     DKCSecurity.l = Top.l /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = Top.l - 1 /\
     DKCp.b{2} /\
     b{2} /\
     DKCp.b{2} = b{2} /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     boundl = SomeGarble.bound /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = Top.l => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> Top.l =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = Top.l => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> Top.l) /\
  i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

   case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#.  

    wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

    case (C.v{1}.[i{1}] = false). wp. swap{2} 2-1. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

     wp. swap{2} 2-1. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

     swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\
     DKCSecurity.bound = C.n{1} + C.q{1} /\
     DKCSecurity.l = Top.l /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = Top.l - 1 /\
     DKCp.b{2} /\
     b{2} /\
     DKCp.b{2} = b{2} /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     boundl = SomeGarble.bound /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = Top.l => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> Top.l =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = Top.l => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> Top.l) /\
  ! i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

     case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

    swap{2} 2-1. wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

    case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#.

     wp. swap{2} 2-1. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

      wp. rnd{2}. swap{2} 2 2. rnd. rnd. wp. rnd (fun b, !b). 
      auto; progress. by rewrite ?DBool.dboolb. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. smt. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. by rewrite DBool.dbool_ll.
      
      idtac=>/#.
      idtac=>/#.
      by rewrite size_set.
      by rewrite ?size_set.
      by rewrite size_set.

      rewrite ?getP ?get_set //=. idtac=>/#. idtac=>/#. rewrite H35 //=. idtac=>/#.  

      rewrite ?getP get_set //=. idtac=>/#. cut -> : l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by simplify. 
  
      rewrite ?getP ?get_set //=. idtac=>/#. case (k = l) => hk. rewrite ?hk H //=. cut ->: C.v{2}.[Top.l] = ! C.v{2}.[Top.l] <=> false by idtac=>/#. simplify. cut ->: l < C.n{2} + C.q{2} - C.m{2} <=> true. cut : 0 <= l < DKCSecurity.bound by idtac=>/#. rewrite H0. progress. move : H12. simplify validInputsP. smt tmo=30. by simplify. simplify. idtac=>/#.  
  
      rewrite ?getP ?get_set //=. idtac=>/#. idtac=>/#.
      rewrite ?getP ?get_set //=. idtac=>/#. 

      wp. skip; progress.
        by idtac=>/#.
        by rewrite size_offun max_ler =>/#.
        by rewrite size_offun max_ler =>/#. 
        by idtac=>/#.
        by rewrite ?map0P. 
        by rewrite ?map0P.    
        by rewrite ?map0P. 
        
        rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. idtac=>/#.
        cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. 
        rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. idtac=>/#.
        rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. idtac=>/#.
        rewrite ?getP. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. 

      wp.
      while (={glob A, real, p, R.t, DKCp.b, DKCp.kpub, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ DKCSecurity.l = Top.l /\
  Top.l = Top.l /\ i{1} = i0{2} /\ lsb1{2} = DKCp.lsb{2} /\
  i{1} = i0{2} /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
  DKCp.b{2} /\ ={useVisible} /\ useVisible{1} /\
  b{2} /\ size R.t{1} = size R.t{2} /\
  i{1} = i0{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
  DKCp.b{2} = b{2} /\ DKCp.b{1} = b{1} /\
  boundl = SomeGarble.bound /\
  GSch.EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
    oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])])).

        auto; progress; first 2 by idtac=>/#. 
        by rewrite size_set.

      wp. 
      while (={glob A, real, p, i, DKCp.kpub, DKCp.b, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ Top.l = DKCSecurity.l /\
  Top.l = Top.l /\ 
   0 <= i{1} <= C.n{1} + C.q{1} /\
  DKCp.b{2} /\ 
  b{2} /\
  DKCp.b{2} = b{2} /\
  boundl = SomeGarble.bound /\
  GSch.EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
     oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])])).

    if. progress. idtac=>/#.
      auto; progress; first 4 by idtac=>/#.
    auto; progress; first 4 by idtac=>/#. 
    auto; progress; first 4 by idtac=>/#.       
      by idtac=>/#. by rewrite size_offun max_ler => /#.
      rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. done. 


(******)
(* END OF RANDOM GENERATION *)
(* BEGIN OF GARBLE *)
(******)

    wp. call (_ : true) => //. wp. inline*.

    while (={glob A, real, p, G.g} /\
    query{1} = query_ind{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    DKCSecurity.l = Top.l /\ l0{1} = l{1} /\
  l{1} = Top.l-1 /\ C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
    DKCp.b{2} /\
    b{2} /\ l0{1} = l{1} /\
    DKCp.b{2} = b{2} /\
    GSch.EncSecurity.queryValid_IND query{1} /\
  ={glob C} /\ size G.yy{1} = size G.yy{2} /\ size G.yy{1} = C.n{1} + C.q{1} /\
  boundl = SomeGarble.bound /\
    size C.v{1} = C.n{1} + C.q{1} /\
    C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
    validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
    C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
    C.v{2}.[i0_0] =
    oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
  (forall (k : int), 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
    R.t{2}.[Top.l] = !DKCp.lsb{2} /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} =>
    R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} => k <> l =>
    R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
  oget R.xx{1}.[(l, ! C.v{1}.[l])] = DKCp.ksec{2} /\ ={G.pp} (*/\
  (forall k a b, 0 <= k < G.g{2} => G.pp{1}.[(k, a, b)] = G.pp{2}.[(k,a,b)])*)). 

  case (! C.aa{2}.[G.g{2}] < l).
  rcondt{2} 3. auto.

  rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 30. auto; progress; smt.
    rcondt{2} 40. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 45. auto; progress; smt.
     rcondt{2} 55. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 60. auto; progress; smt.

  auto; progress.
  by smt.
        idtac=>/#. idtac=>/#.
        by rewrite ?size_set. by rewrite ?size_set. 

       cut ->: C.aa{2}.[G.g{2}] <= Top.l - 1 <=> false by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l - 1 <=> false by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. smt. case(C.bb{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. smt. by rewrite H15; first by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. smt. case(C.bb{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. smt. by rewrite H15; first by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
     idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (oget
              C.gg{2}.[(G.g{2}, ! C.v{2}.[C.aa{2}.[G.g{2}]],
                        C.v{2}.[C.bb{2}.[G.g{2}]])] = C.v{2}.[G.g{2}]) => hc. rewrite hc. by move : H15; simplify validInputsP valid_circuitP fst snd => /#. cut ? : oget
      C.gg{2}.[(G.g{2}, ! C.v{2}.[C.aa{2}.[G.g{2}]],
                C.v{2}.[C.bb{2}.[G.g{2}]])] =
   ! C.v{2}.[G.g{2}] by idtac=>/#. rewrite H26. cut ->: C.v{2}.[G.g{2}] ^^ ! C.v{2}.[G.g{2}] <=> true by idtac=>/#. rewrite xor_true. rewrite H16. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. trivial. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 


  rcondf{2} 3. progress. auto.

  case (C.bb{2}.[G.g{2}] = l).
  rcondt{2} 3. auto; progress; smt.

  rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt. 
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 46. auto; progress; smt. 
     rcondt{2} 56. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress; smt. 

    wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
  by smt.
        idtac=>/#. idtac=>/#.
        by rewrite ?size_set. by rewrite ?size_set. 

       cut ->: C.aa{2}.[G.g{2}] <= Top.l - 1 <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l - 1 <=> false by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : Top.l <= C.bb{2}.[G.g{2}] by idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

    case (! C.bb{2}.[G.g{2}] <= l).
    rcondt{2} 3. auto; progress; smt.
    rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt. 
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 46. auto; progress; smt. 
     rcondt{2} 56. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress. 

  wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
  by smt. 
  idtac=>/#. idtac=>/#.
        by rewrite ?size_set. by rewrite ?size_set. 
 
   cut ->: C.aa{2}.[G.g{2}] <= Top.l - 1 <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l - 1 <=> false by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : Top.l <= C.bb{2}.[G.g{2}] by idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

     rcondf{2} 3. auto. progress. smt.
     rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt. 
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 46. auto; progress; smt. 
     rcondt{2} 57. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 62. auto; progress. 

    auto. progress.
    by smt. 
  idtac=>/#. 
        by rewrite ?size_set. by rewrite ?size_set. 
 
   cut ->: C.aa{2}.[G.g{2}] <= Top.l - 1 <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l - 1 <=> true by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

  auto. progress.
  by idtac=>/#.
  by rewrite size_offun max_ler => /#.
  admit.
  by idtac=>/#.
  rcondf {1} 1. by auto.

  rcondf{2} 11. progress. wp. while ((glob A){m} = (glob A) /\ query{m} = query_ind /\ (forall (plain : fun_t * input_t), let (n, m, q, aa, bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = Top.l /\ boundl = SomeGarble.bound /\ l{m} = Top.l - 1 /\ DKCp.b /\ b /\ DKCp.b = b /\ ! (GSch.EncSecurity.queryValid_IND query{m})). if. auto. auto. auto. auto. while {2} (={glob A} /\ query{1} = query_ind{2} /\ (forall (plain : fun_t * input_t), let (n, m, q, aa, bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = Top.l /\ boundl = SomeGarble.bound /\ l{1} = Top.l - 1 /\ b{2} /\ DKCp.b{2} = b{2} /\ ! (GSch.EncSecurity.queryValid_IND query{1})) (DKCSecurity.bound{2} - i{2}). progress. if. auto. progress. smt. smt. smt. idtac=>/#. auto. progress. smt. smt. idtac=>/#. 
   auto. progress. idtac=>/#. idtac=>/#.
qed.


lemma GameHybrid_l_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = l /\ DKCSecurity.boundl = SomeGarble.bound /\ l{1} = l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} ==> res{1} <> res{2}].
proof.
move => Agen_ll Aget_ll.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  swap{2} 11 -10.
  seq 1 1 : (={glob A} /\ query{1} = query_ind{2} /\
    (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\
    DKCSecurity.l = Top.l /\ DKCSecurity.boundl = SomeGarble.bound /\
    l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}); first by call (_ : true).

  case (GSch.EncSecurity.queryValid_IND query{1}).
    rcondt{1} 1; first by progress.
    rcondt{2} 11; first by auto; (while (true); first by auto); auto. 
    swap{2} 11 -10.
    swap{2} 12 -10.
    swap{2} 13 -10.
    seq 3 3 : ((={glob A,real,p} /\
      query{1} = query_ind{2} /\ 
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\ DKCSecurity.boundl = SomeGarble.bound /\
      l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
      GSch.EncSecurity.queryValid_IND query{1} /\ ={glob C} /\
      size C.v{1} = (C.n + C.q){1} /\
      C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
      validInputsP (C.f, C.x){1} /\
      (forall i, 0 <= i < C.n{2} => C.v{2}.[i] = C.x{2}.[i]) /\
      (forall i, C.n <= i < C.n + C.q => C.v{2}.[i] = oget C.gg.[(i, C.v{2}.[C.aa{2}.[i]], C.v{2}.[C.bb.[i]])]){2}).
      call CircuitInitEquiv.
      auto; progress. 
        by move : H4; rewrite /queryValid_IND /valid_plain /validInputs /validInputsP ?valid_wireinput /valid_circuitP /fst /snd; case realL => /#. 
        simplify validBound; case realL => /#.

    seq 1 11 : (={glob A, real, p} /\
      query{1} = query_ind{2} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\ 
      l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\
      GSch.EncSecurity.queryValid_IND query{1} /\
      ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
      size C.v{1} = C.n{1} + C.q{1} /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
      (forall (i0 : int), 0 <= i0 < C.n{2} => C.v{2}.[i0] = C.x{2}.[i0]) /\
      (forall (i0 : int),
        C.n{2} <= i0 < C.n{2} + C.q{2} =>
        C.v{2}.[i0] =
        oget C.gg{2}.[(i0, C.v{2}.[C.aa{2}.[i0]], C.v{2}.[C.bb{2}.[i0]])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
      R.t{2}.[l] = !DKCp.lsb{2} /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
      oget R.xx{1}.[(l, !C.v{1}.[l])] = DKCp.ksec{2}).
    
      inline RandomInit.init AdvRandomInit(DKC).init.

      transitivity{2} {
        DKCp.lsb = witness;
        DKCp.ksec = witness;
        DKCp.used = fset0;
        DKCp.kpub = map0;
        i = 0;
        while (i < C.n + C.q) {
          if (i = l) {
            DKCp.lsb = ${0,1};
            DKCp.ksec = $Dword.dwordLsb (DKCp.lsb);
            DKCp.kpub.[(i,DKCp.lsb)] = witness;
            DKCp.kpub.[(i,!DKCp.lsb)] = $Dword.dwordLsb (!DKCp.lsb); (* can never return or encrypt this key *)
          }
          else {
            tok1 = $Dword.dwordLsb (false);
            tok2 = $Dword.dwordLsb (true);
            DKCp.kpub.[(i, false)] = tok1;
            DKCp.kpub.[(i, true)] = tok2;
          }
          i = i + 1;
        }
        useVisible = true;
        R.t = offun (fun (_ : int) => false) (C.n + C.q);
        i = 0;
        while (i < C.n + C.q) {
          trnd =$ {0,1};
          v = if useVisible then C.v.[i] else false;
          trnd = if i < C.n + C.q - C.m then trnd else v;
          R.t.[i] = trnd;
          i = i + 1;
        }
        R.t.[l] = !DKCp.lsb;
      }
      ( (={glob A, real, p} /\
          query{1} = query_ind{2} /\
        DKCSecurity.bound = C.n{1} + C.q{1} /\
        DKCSecurity.l = Top.l /\ 
          l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
        GSch.EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
        (forall (i1 : int),
          C.n{2} <= i1 < C.n{2} + C.q{2} =>
          C.v{2}.[i1] =
          oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])])

        ==>

        ={glob A, real, p} /\
        query{1} = query_ind{2} /\
          DKCSecurity.bound = C.n{1} + C.q{1} /\
          DKCSecurity.l = Top.l /\
        l{1} = Top.l /\ 
          !DKCp.b{2} /\
          !b{2} /\
          DKCp.b{2} = b{2} /\
        GSch.EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
        R.t{1}.[l] = !DKCp.lsb{2} /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
        oget R.xx{1}.[(l, !C.v{1}.[l])] = DKCp.ksec{2}
      )
      
      ( (={glob A, real, p, DKCp.b, b, query_ind} /\
          query_ind{1} = query_ind{2} /\
        DKCSecurity.bound = C.n{1} + C.q{1} /\
        DKCSecurity.l = Top.l /\ 
          !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
        GSch.EncSecurity.queryValid_IND query_ind{1} /\
        ={glob C} /\ DKCSecurity.boundl = SomeGarble.bound /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
        (forall (i1 : int),
          C.n{2} <= i1 < C.n{2} + C.q{2} =>
          C.v{2}.[i1] =
          oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])])

        ==> 

        ={glob A, real, p, R.t, DKCp.b, DKCp.kpub, b, DKCp.lsb, DKCp.ksec, query_ind} /\
          DKCSecurity.bound = C.n{1} + C.q{1} /\
          DKCSecurity.l = Top.l /\
         i{1} = i0{2} /\
          !DKCp.b{2} /\
          !b{2} /\ i{1} = i0{2} /\ 
          DKCp.b{2} = b{2} /\ DKCSecurity.boundl = SomeGarble.bound /\
        GSch.EncSecurity.queryValid_IND query_ind{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        R.t{2}.[l] = !DKCp.lsb{2})
          .

          progress. exists (glob A){2}. exists C.aa{2}. exists C.bb{2}. exists (((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2})). exists (C.gg{2}). exists C.m{2}. exists C.n{2}.  exists C.q{2}. exists C.v{2}. exists (C.x{2}).      exists (b{2}). exists (b{2}). exists (p{2}). exists (query_ind{2}).  exists (real{2}). by progress. by progress. 

      swap{2} 7 -4. swap{2} 8 -5. fusion{2} 8!1 @ 1,4.
      
      wp.
      
  while (={glob A, real, p, i} /\
    query{1} = query_ind{2} /\ ={useVisible} /\ useVisible{2} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
    l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\
      GSch.EncSecurity.queryValid_IND query{1} /\ size R.t{1} = C.n{1} + C.q{1} /\
    ={glob C} /\ size R.t{1} = size R.t{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
      size C.v{1} = C.n{1} + C.q{1} /\ DKCSecurity.boundl = SomeGarble.bound /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
    (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
    (forall (i1 : int),
      C.n{2} <= i1 < C.n{2} + C.q{2} =>
      C.v{2}.[i1] =
      oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
    (forall k, 0 <= k < i{1} => k <> l => R.t{1}.[k] = R.t{2}.[k]) /\
    (forall k, 0 <= k < i{1} => k = l => R.t{1}.[k] = !DKCp.lsb{2}) /\
    (forall k, 0 <= k < i{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k = l => oget R.xx{1}.[(k,!C.v{1}.[k])] = DKCp.ksec{2})).
  
    if{2}; last first.

  case ((i < C.n + C.q - C.m){1}).
    swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\
     DKCSecurity.bound = C.n{1} + C.q{1} /\
     DKCSecurity.l = Top.l /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = Top.l /\
     !DKCp.b{2} /\
     !b{2} /\
     DKCp.b{2} = b{2} /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     boundl = SomeGarble.bound /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = Top.l => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> Top.l =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = Top.l => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> Top.l) /\
  i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

   case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#.  

    wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

    case (C.v{1}.[i{1}] = false). wp. swap{2} 2-1. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

     wp. swap{2} 2-1. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

     swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\
     DKCSecurity.bound = C.n{1} + C.q{1} /\
     DKCSecurity.l = Top.l /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = Top.l /\
     !DKCp.b{2} /\
     !b{2} /\
     DKCp.b{2} = b{2} /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     boundl = SomeGarble.bound /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = Top.l => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> Top.l =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = Top.l => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> Top.l) /\
  ! i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

     case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

    swap{2} 2-1. wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

    case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#.

     wp. swap{2} 2-1. rnd. rnd. wp. auto; progress. smt. smt. smt. smt. smt. smt. by rewrite size_set. by rewrite ?size_set. by rewrite ?size_set. rewrite ?get_set. idtac=>/#. idtac=>/#. idtac=>/#. rewrite get_set => /#. rewrite ?getP H //=. smt. rewrite ?getP H //=. smt tmo=10. rewrite ?getP H //=. idtac=>/#. 

      wp. rnd{2}. swap{2} 2 2. rnd. rnd. wp. rnd (fun b, !b). 
      auto; progress. by rewrite ?DBool.dboolb. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. smt. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. by rewrite DBool.dbool_ll.
      
      idtac=>/#.
      idtac=>/#.
      by rewrite size_set.
      by rewrite ?size_set.
      by rewrite size_set.

      rewrite ?getP ?get_set //=. idtac=>/#. idtac=>/#. rewrite H35 //=. idtac=>/#.  

      rewrite ?getP get_set //=. idtac=>/#. cut -> : l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by simplify. 
  
      rewrite ?getP ?get_set //=. idtac=>/#. case (k = l) => hk. rewrite ?hk H //=. cut ->: C.v{2}.[Top.l] = ! C.v{2}.[Top.l] <=> false by idtac=>/#. simplify. cut ->: l < C.n{2} + C.q{2} - C.m{2} <=> true. cut : 0 <= l < DKCSecurity.bound by idtac=>/#. rewrite H0. progress. move : H12. simplify validInputsP. smt tmo=30. by simplify. simplify. idtac=>/#.  
  
      rewrite ?getP ?get_set //=. idtac=>/#. idtac=>/#.
      rewrite ?getP ?get_set //=. idtac=>/#. 

      wp. skip; progress.
        by idtac=>/#.
        by rewrite size_offun max_ler =>/#.
        by rewrite size_offun max_ler =>/#. 
        by idtac=>/#.
        by rewrite ?map0P. 
        by rewrite ?map0P.    
        by rewrite ?map0P. 
        
        rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. idtac=>/#.
        cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. 
        rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. idtac=>/#.
        rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. idtac=>/#.
        rewrite ?getP. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. 

      wp.
      while (={glob A, real, p, R.t, DKCp.b, DKCp.kpub, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ DKCSecurity.l = Top.l /\
  Top.l = Top.l /\ i{1} = i0{2} /\ lsb1{2} = DKCp.lsb{2} /\
  i{1} = i0{2} /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
  !DKCp.b{2} /\ ={useVisible} /\ useVisible{1} /\
  !b{2} /\ size R.t{1} = size R.t{2} /\
  i{1} = i0{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
  DKCp.b{2} = b{2} /\ DKCp.b{1} = b{1} /\
  boundl = SomeGarble.bound /\
  GSch.EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
    oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])])).

        auto; progress; first 2 by idtac=>/#. 
        by rewrite size_set.

      wp. 
      while (={glob A, real, p, i, DKCp.kpub, DKCp.b, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ Top.l = DKCSecurity.l /\
  Top.l = Top.l /\ 
   0 <= i{1} <= C.n{1} + C.q{1} /\
  !DKCp.b{2} /\ 
  !b{2} /\
  DKCp.b{2} = b{2} /\
  boundl = SomeGarble.bound /\
  GSch.EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
     oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])])).

    if. progress. idtac=>/#.
      auto; progress; first 4 by idtac=>/#.
    auto; progress; first 4 by idtac=>/#. 
    auto; progress; first 4 by idtac=>/#.       
      by idtac=>/#. by rewrite size_offun max_ler => /#.
      rewrite get_set. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. idtac=>/#. done. 


(******)
(* END OF RANDOM GENERATION *)
(* BEGIN OF GARBLE *)
(******)

   wp. call (_ : true) => //. wp. inline*.

    while (={glob A, real, p, G.g} /\
    query{1} = query_ind{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    DKCSecurity.l = Top.l /\ l0{1} = l{1} /\
  l{1} = Top.l /\ C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
    !DKCp.b{2} /\
    !b{2} /\ l0{1} = l{1} /\
    DKCp.b{2} = b{2} /\
    GSch.EncSecurity.queryValid_IND query{1} /\
  ={glob C} /\ size G.yy{1} = size G.yy{2} /\ size G.yy{1} = C.n{1} + C.q{1} /\
  boundl = SomeGarble.bound /\
    size C.v{1} = C.n{1} + C.q{1} /\
    C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
    validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
    C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
    C.v{2}.[i0_0] =
    oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
  (forall (k : int), 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
    R.t{2}.[Top.l] = !DKCp.lsb{2} /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} =>
    R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} => k <> l =>
    R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
  oget R.xx{1}.[(l, ! C.v{1}.[l])] = DKCp.ksec{2} /\ ={G.pp} (*/\
  (forall k a b, 0 <= k < G.g{2} => G.pp{1}.[(k, a, b)] = G.pp{2}.[(k,a,b)])*)). 

  case (!C.aa{2}.[G.g{2}] <= l).
  rcondt{2} 3. auto. progress; smt.

  rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 30. auto; progress; smt.
    rcondt{2} 40. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 45. auto; progress; by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 
     rcondt{2} 55. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 60. auto; progress; by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

  auto; progress.
  by smt.
        idtac=>/#. idtac=>/#.
        by rewrite ?size_set. by rewrite ?size_set. 

       cut ->: C.aa{2}.[G.g{2}] <= Top.l <=> false by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l <=> false by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. smt. case(C.bb{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. smt. by rewrite H15; first by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. smt. case(C.bb{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. smt. by rewrite H15; first by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
     idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (oget
              C.gg{2}.[(G.g{2}, ! C.v{2}.[C.aa{2}.[G.g{2}]],
                        C.v{2}.[C.bb{2}.[G.g{2}]])] = C.v{2}.[G.g{2}]) => hc. rewrite hc. by move : H15; simplify validInputsP valid_circuitP fst snd => /#. cut ? : oget
      C.gg{2}.[(G.g{2}, ! C.v{2}.[C.aa{2}.[G.g{2}]],
                C.v{2}.[C.bb{2}.[G.g{2}]])] =
   ! C.v{2}.[G.g{2}] by idtac=>/#. rewrite H26. cut ->: C.v{2}.[G.g{2}] ^^ ! C.v{2}.[G.g{2}] <=> true by idtac=>/#. rewrite xor_true. rewrite H16. idtac=>/#. cut ? : 0 <= l < C.n{2} + C.q{2} - C.m{2}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. trivial. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 
  
  case (C.aa{2}.[G.g{2}] = l).
  rcondt{2} 3. auto. progress; smt.      

  rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt.
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 46. auto; progress. rewrite H20. rewrite xor_false H14. cut ->: DKCp.lsb{hr} = !DKCp.lsb{hr} <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 
     rcondt{2} 56. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress; by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

  wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
  by smt.
        idtac=>/#. idtac=>/#.
        by rewrite ?size_set. by rewrite ?size_set. 

       cut ->: C.aa{2}.[G.g{2}] <= Top.l <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l <=> false by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. smt. case(C.bb{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. smt. by rewrite H15; first by move : H10; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. smt. case(C.bb{2}.[G.g{2}] = DKCSecurity.l && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. smt. by rewrite H15; first by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
     idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H13; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#.  rewrite H13. idtac=> /#. rewrite H13. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. done. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 


  rcondf{2} 3. progress. auto. progress. smt.

  case (C.bb{2}.[G.g{2}] = l).
  rcondt{2} 3. auto; progress; smt.

  rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt. 
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 46. auto; progress; smt. 
     rcondt{2} 57. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 62. auto; progress; smt. 

     auto; progress.
  by smt.
        idtac=>/#. 
        by rewrite ?size_set. by rewrite ?size_set. 

       cut ->: C.aa{2}.[G.g{2}] <= Top.l <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l <=> true by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

    case (! C.bb{2}.[G.g{2}] <= l).
    rcondt{2} 3. auto; progress; smt.
    rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt. 
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 46. auto; progress; smt. 
     rcondt{2} 56. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress. 

  wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
  by smt. 
  idtac=>/#. idtac=>/#.
        by rewrite ?size_set. by rewrite ?size_set. 
 
   cut ->: C.aa{2}.[G.g{2}] <= Top.l <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l <=> false by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : Top.l <= C.bb{2}.[G.g{2}] by idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

     rcondf{2} 3. auto. progress. smt.
     rcondt{2} 10. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. smt. 
    rcondt{2} 25. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress; smt. 
    rcondt{2} 41. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 46. auto; progress; smt. 
     rcondt{2} 57. progress. auto. progress. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ? : 0 <= l < C.n{hr} + C.q{hr} - C.m{hr}. cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 62. auto; progress. 

    auto. progress.
    by smt. 
  idtac=>/#. 
        by rewrite ?size_set. by rewrite ?size_set. 
 
   cut ->: C.aa{2}.[G.g{2}] <= Top.l <=> true by idtac=>/#.
       cut ->: C.bb{2}.[G.g{2}] <= Top.l <=> true by move : H10; simplify validInputsP valid_circuitP fst snd => /#.
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H13; first 2 by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. cut ->: C.aa{2}.[G.g{2}] = DKCSecurity.l <=> false by idtac=>/#. simplify. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. by move : H10; simplify validInputsP valid_circuitP fst snd => /#. 

auto. progress.
  by idtac=>/#.
  by rewrite size_offun max_ler => /#.
  admit.
  by idtac=>/#.
  rcondf {1} 1. by auto.

  rcondf{2} 11. progress. wp. while ((glob A){m} = (glob A) /\ query{m} = query_ind /\ (forall (plain : fun_t * input_t), let (n, m, q, aa, bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = Top.l /\ boundl = SomeGarble.bound /\ l{m} = Top.l /\ !DKCp.b /\ !b /\ DKCp.b = b /\ ! (GSch.EncSecurity.queryValid_IND query{m})). if. auto. auto. auto. auto. while {2} (={glob A} /\ query{1} = query_ind{2} /\ (forall (plain : fun_t * input_t), let (n, m, q, aa, bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = Top.l /\ boundl = SomeGarble.bound /\ l{1} = Top.l /\ !b{2} /\ DKCp.b{2} = b{2} /\ ! (GSch.EncSecurity.queryValid_IND query{1})) (DKCSecurity.bound{2} - i{2}). progress. if. auto. progress. smt. smt. smt. idtac=>/#. auto. progress. smt. smt. idtac=>/#. 
   auto. progress. idtac=>/#. idtac=>/#. 
qed.

lemma GameHybrid_l_sim_pr (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>
  !DKCp.b{m} =>  
  Pr[GameHybrid(A).garble(l)@ &m: res] =
  Pr[DKCSecurity.Game(DKC, DKC_Adv(DKCSecurity.DKC, A)).game(false)@ &m: !res].
proof. by move=> AgenLL AgetL hb; byequiv (GameHybrid_l_sim A _ _) => //= /#. qed. 

lemma GameHybrid_l1_sim_pr (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>
  DKCp.b{m} =>  
  Pr[GameHybrid(A).garble(l-1)@ &m: res] =
  Pr[DKCSecurity.Game(DKC, DKC_Adv(DKCSecurity.DKC, A)).game(true)@ &m: res].
proof. by move=> AgenLL AgetL hb; byequiv (GameHybrid_l1_sim A _ _) => //= /#. qed.
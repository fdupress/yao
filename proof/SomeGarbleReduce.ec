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
  proc query_tokens (rn : bool, alpha : bool, betha : bool) : word = {
    var twe : word;
    var gamma, pos : bool;
    var i,j : int;
    var ki, kj, zz : word;

    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ betha);
    gamma = C.v.[G.g] ^^ oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ betha)];

    (*pos = if G.a = l then true else false;
    i = if G.a = l then 2*G.b + bti (R.t.[G.b] ^^ betha) else 2*G.a + bti (R.t.[G.a] ^^ alpha);
    j = $[2*(G.g + C.n + C.q) .. 2*(G.g + C.n + C.q)+1];
    j = if rn then j else 2*(G.g + C.n + C.q);*)

    (ki,kj,zz) = D.encrypt((G.a,alpha),(G.b,betha),(G.g, gamma),twe);

    (*G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ betha)] = zz;*)
    
    if (G.a = l) {
      R.xx.[(G.b, C.v.[G.b] ^^ betha)] = oget DKCp.kpub.[(G.b, C.v.[G.b] ^^ betha)];
    }
    else {
      R.xx.[(G.a, C.v.[G.a] ^^ alpha)] = oget DKCp.kpub.[(G.a, C.v.[G.a] ^^ alpha)];
    }

    if (!rn) {
      R.xx.[(G.g, C.v.[G.g] ^^ gamma)] = oget DKCp.kpub.[(G.g, C.v.[G.g] ^^ gamma)];
    }

    return kj;
  }
  
  proc init(useVisible:bool): unit = {
    var v, trnd, i;
      
    R.t = offun (fun x, false) (C.n + C.q);
    R.xx = map0;

    i = 0;
    while (i < C.n + C.q) {
      if (i = l) {
        trnd = D.get_lsb();

        R.t.[i] = !trnd;
      }

      else {
        trnd = ${0,1};
        v = if useVisible then C.v.[i] else false;
        trnd = if (i < C.n + C.q - C.m) then trnd else v;
        
        R.t.[i] = trnd;
      }
      i = i + 1;
    }
  }
}.
  
module AdvInit (D : DKC_t) = {
    
  proc garb(yy : word, alpha : bool, bet : bool) : unit = {
    var twe, aa, bb : word;
        
    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ bet);
    aa = oget R.xx.[(G.a, C.v.[G.a] ^^ alpha)];
    bb = oget R.xx.[(G.b, C.v.[G.b] ^^ bet)];
    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ bet)] = E twe aa bb yy;
  }

  proc garb'(rn : bool, alpha : bool, bet : bool) : word = {
    var yy : word;
      
    yy = $Dword.dword;
    yy = if rn then yy else oget R.xx.[(G.g, oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ bet)])];
    garb(yy, alpha, bet);
    return yy;
  }

    proc query_garble (rn : bool, alpha : bool, betha : bool) : word = {
    var twe : word;
    var gamma, pos : bool;
    var i,j : int;
    var ki, kj, zz : word;

    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ betha);
    gamma = C.v.[G.g] ^^ oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ betha)];

    (ki,kj,zz) = D.encrypt((G.a,alpha),(G.b,betha),(G.g, gamma),twe);

    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ betha)] = zz;

    return kj;
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

      garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
        
      if (G.a <> l /\ G.b <> l) {
        garb'(G.a <= l, true, false);
        garb'(G.b <= l, false, true);
        G.yy.[G.g] = garb'(G.a <= l, true, true);

        if (G.a <= l < G.b /\ C.gg.[(G.g, !C.v.[G.a], false)] = C.gg.[(G.g, !C.v.[G.a], true)]) {
          garb(G.yy.[G.g], true, false);
        }
      }
 
      else {
        if (G.a = l) {
          garb'(false,false,true);
        }

        else {
          garb'(true,true,false);

          if (C.gg.[(G.g, !C.v.[G.a], false)] = C.gg.[(G.g, !C.v.[G.a], true)]) {
            garb(G.yy.[G.g], true, false);
          }
        }
      }
      
      G.g = G.g + 1;
    }
  }
}.

require import SomeGarbleHy.

module DKC_Adv (D : DKC_t, Adv_IND : GSch.EncSecurity.Adv_IND_t) : Adv_DKC_t = {

  proc get_challenge () : bool = {
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
      AdvRandomInit(D).init(true);
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

module M1 = {
  proc main(useVisible:bool) : unit = {
    var i,i0 : int;
    var v, trnd : bool;
    
    DKCp.used = FSet.fset0;
     
    DKCp.kpub = map0;
    DKCp.rr = map0;
      
    i = 0;
    while (i < DKCSecurity.bound) {
      DKCp.kpub.[(i, false)] = $Dword.dwordLsb (false);
      DKCp.kpub.[(i, true)] = $Dword.dwordLsb (true);
      DKCp.rr.[(i,false)] = $Dword.dword;
      DKCp.rr.[(i,true)] = $Dword.dword;
      i = i + 1;
    }

    R.t = offun (fun (_ : int) => false) (C.n + C.q);
    R.xx = map0;

    i0 = 0;
    while (i0 < C.n + C.q) {
      trnd = ${0,1};
      v = if useVisible then C.v.[i0] else false;
      trnd = if i0 < C.n + C.q - C.m then trnd else v;
      R.t.[i0] = if i0 = Top.l then !DKCp.lsb else trnd;

      i0 = i0 + 1;
    }
  }
}.

module M2 = {
  proc main(useVisible:bool) : unit = {
    var i : int;
    var v, trnd : bool;
    
    DKCp.used = FSet.fset0;
     
    DKCp.kpub = map0;
    DKCp.rr = map0;
      
    i = 0;
    while (i < C.n + C.q) {
      DKCp.kpub.[(i, false)] = $Dword.dwordLsb (false);
      DKCp.kpub.[(i, true)] = $Dword.dwordLsb (true);
      DKCp.rr.[(i,false)] = $Dword.dword;
      DKCp.rr.[(i,true)] = $Dword.dword;
      i = i + 1;
    }

    R.t = offun (fun (_ : int) => false) (C.n + C.q);
    R.xx = map0;

    i = 0;
    while (i < C.n + C.q) {
      trnd = ${0,1};
      v = if useVisible then C.v.[i] else false;
      trnd = if i < C.n + C.q - C.m then trnd else v;
      R.t.[i] = if i = Top.l then !DKCp.lsb else trnd;

      i = i + 1;
    }
  }
}.

lemma GameHybrid_l_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = l /\ DKCSecurity.boundl = SomeGarble.bound /\ l{1} = l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} ==> res{1} = !res{2}].
proof.  
  move => Agen_ll Aget_ll.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  swap{2} 6 -5.
  seq 1 1 : (={glob A} /\ query{1} = query_ind{2} /\
    (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\
    DKCSecurity.l = Top.l /\ DKCSecurity.boundl = SomeGarble.bound /\
    l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}); first by call (_ : true).

  case (GSch.EncSecurity.queryValid_IND query{1}).
    rcondt{1} 1; first by progress.
    rcondt{2} 6; first by auto; (while (true); first by auto); auto. 
    swap{2} 6 -5.
    swap{2} 7 -5.
    swap{2} 8 -5.
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

    seq 1 6 : (={glob A, real, p} /\
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
      (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R.xx{1}.[(k, C.v{1}.[k])]) = R.t{1}.[k]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R.xx{1}.[(k, !C.v{1}.[k])]) = !R.t{1}.[k]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k,R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k,!R.t{2}.[k])])).
    
      inline RandomInit.init AdvRandomInit(DKC).init.

  transitivity{2} {
        DKCp.used = fset0;
        DKCp.kpub = map0;
        DKCp.rr = map0;
        i = 0;
        while (i < C.n + C.q) {
          DKCp.kpub.[(i, false)] =$ Dword.dwordLsb false;
          DKCp.kpub.[(i, true)] =$ Dword.dwordLsb true;
          i = i + 1;       
        }
        useVisible = true;
        R.t = offun (fun (_ : int) => false) (C.n + C.q);
        R.xx = map0;
        i = 0;
        while (i < C.n + C.q) {
          if (i = l) {
            trnd = DKC.get_lsb();
            R.t.[i] = !trnd;
          }
          else {
            trnd =$ {0,1};
            v = if useVisible then C.v.[i] else false;
            trnd = if i < C.n + C.q - C.m then trnd else v;
            R.t.[i] = trnd;
          }
          i = i + 1;
        }
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
          R.t{2}.[l] = !DKCp.lsb{2} /\
        (forall (k : int),
          0 <= k < C.n{1} + C.q{1} =>
          getlsb (oget R.xx{1}.[(k, C.v{1}.[k])]) = R.t{1}.[k]) /\
        (forall (k : int),
          0 <= k < C.n{1} + C.q{1} =>
          getlsb (oget R.xx{1}.[(k, ! C.v{1}.[k])]) = ! R.t{1}.[k]) /\
        (forall (k : int),
          0 <= k < C.n{1} + C.q{1} =>
          R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
        (forall (k : int),
          0 <= k < C.n{1} + C.q{1} =>
          R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{2}.[k])])
      )
      
      ( (={glob A, real, p} /\
          query_ind{1} = query_ind{2} /\
        DKCSecurity.bound = C.n{1} + C.q{1} /\
        DKCSecurity.l = Top.l /\ 
          l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
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

        ={glob A, real, p, R.t, DKCp.kpub, query_ind} /\
          DKCSecurity.bound = C.n{1} + C.q{1} /\
          DKCSecurity.l = Top.l /\
        l{1} = Top.l /\ i{1} = i0{2} /\
          !DKCp.b{2} /\
          !b{2} /\
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
        ={R.t, DKCp.kpub} /\ R.t{2}.[l] = !DKCp.lsb{2} )
          .

          progress. exists (glob A){2}. exists (b{2}). exists (((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2})). exists (C.x{2}). exists C.n{2}. exists C.m{2}. exists C.q{2}. exists C.aa{2}. exists C.bb{2}. exists (C.gg{2}). exists C.v{2}. exists (b{2}). exists (query_ind{2}). exists (p{2}). exists (real{2}). by progress. by progress. 

      swap{2} 7 -4. swap{2} 8 -5. swap{2} 8 -4. fusion{2} 8!1 @ 2,1.
      
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
    (forall k, 0 <= k < i{1} => getlsb (oget R.xx{1}.[(k, C.v{1}.[k])]) = R.t{1}.[k]) /\
    (forall k, 0 <= k < i{1} => getlsb (oget R.xx{1}.[(k, !C.v{1}.[k])]) = !R.t{1}.[k]) /\
    (forall k, 0 <= k < i{1} => R.t{1}.[k] = R.t{2}.[k]) /\
    (forall k, 0 <= k < i{1} => k = l => R.t{2}.[k] = !DKCp.lsb{2}) /\
    (forall k, 0 <= k < i{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k,R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k,!R.t{1}.[k])])).

  case (i{2} = l).
      rcondt{2} 3; first by auto.
      inline DKC.get_lsb. swap{2} 3 -2. wp. rnd{2}. rnd. rnd. wp. rnd (fun b, !b).
      auto; progress; first 6 by smt.
      by rewrite Dword.dwordLsb_lossless.
      idtac=>/#.
      idtac=>/#.
      by rewrite size_set.
      by rewrite ?size_set.
      by rewrite size_set.

      rewrite ?getP get_set //=. idtac=>/#. case (k = l) => hk. simplify. rewrite H ?hk //=. cut ->: C.v{2}.[l] = ! (C.v{2}.[l]) <=> false by idtac=>/#. simplify. rewrite oget_some. rewrite H in H27. simplify H27. rewrite (Dword.lsb_dwordLsb (if l < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[l]) _). exact H27. done. simplify. idtac=>/#.

      rewrite ?getP get_set //=. idtac=>/#. case ( k = l) => hk. simplify. rewrite H ?hk //=. rewrite oget_some. rewrite H in H30. simplify H30. rewrite (Dword.lsb_dwordLsb (!(if l < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[l])) _). exact H30. done. simplify. idtac=>/#.

      cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. rewrite ?get_set => /#. 
      rewrite ?get_set => /#. 
  
      cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. rewrite ?getP //=. case (k = l) => hc //=. rewrite H ?hc //=. cut ->: C.v{2}.[l] = ! C.v{2}.[l] <=> false by idtac=>/#. simplify. cut ->: R.t{1}.[l <- if l < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[l]].[l] = false <=> true by smt. simplify. cut ->: R.t{1}.[l <- if l < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[l]].[l] = true <=> false by smt. by simplify. smt. 
  
      rewrite ?getP //=. case (k = l) => hc //=. rewrite H ?hc //=. cut ->: (!R.t{1}.[l <- if l < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[l]].[l]) = false <=> false by smt. simplify. cut ->: (!R.t{1}.[l <- if l < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[l]].[l]) = true <=> true by smt tmo=30. by simplify. smt.   

      rcondf{2} 3; first by auto.
      swap{2} 3-2. wp. rnd. rnd. wp. rnd. (auto; progress; first 4 by smt); first 2 by idtac=>/#.

      by rewrite size_set.
      by rewrite ?size_set.
      by rewrite size_set.

      rewrite ?getP get_set //=. idtac=>/#. case ( k = i{2}) => hk. simplify. rewrite H ?hk //=. cut ->: C.v{2}.[i{2}] = ! (C.v{2}.[i{2}]) <=> false by idtac=>/#. simplify. rewrite oget_some. rewrite H in H27. simplify H27. rewrite (Dword.lsb_dwordLsb (if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}]) _). exact H27. done. simplify. idtac=>/#.

      rewrite ?getP get_set //=. idtac=>/#. case ( k = i{2}) => hk. simplify. rewrite H ?hk //=. rewrite oget_some. rewrite H in H30. simplify H30. rewrite (Dword.lsb_dwordLsb (!(if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}])) _). exact H30. done. simplify. idtac=>/#.

      rewrite ?get_set => /#. 
      rewrite ?get_set => /#. 
  
      rewrite ?getP //=. case (k = i{2}) => hc //=. rewrite H ?hc //=. cut ->: C.v{2}.[i{2}] = ! C.v{2}.[i{2}] <=> false by idtac=>/#. simplify. cut ->: R.t{1}.[i{2} <- if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}]].[i{2}] = false <=> true by smt tmo=30. simplify. cut ->: R.t{1}.[i{2} <- if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}]].[i{2}] = true <=> false by smt tmo=30. by simplify. smt. 
  
      rewrite ?getP //=. case (k = i{2}) => hc //=. rewrite H ?hc //=. cut ->: (!R.t{1}.[i{2} <- if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}]].[i{2}]) = false <=> false by smt tmo=30. simplify. cut ->: (!R.t{1}.[i{2} <- if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}]].[i{2}]) = true <=> true by smt tmo=30. by simplify. smt.   

      wp. skip; progress.
        by idtac=>/#.
        by rewrite size_offun max_ler =>/#.
        by rewrite size_offun max_ler =>/#.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#.     
        by rewrite ?map0P. 
        by rewrite ?map0P. 
        by idtac=>/#.
        cut ? : 0 <= l < SomeGarble.bound by rewrite l_pos. idtac=>/#.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#.
        by idtac=>/#. 

sim. admit.

      rewrite ?getP //=. case (k = i{2}) => hc //=. rewrite H ?hc //=. cut ->: C.v{2}.[i{2}] = ! C.v{2}.[i{2}] <=> false by idtac=>/#. simplify. simplify. cut ->: (!R.t{1}.[i{2} <- if i{2} < C.n{2} + C.q{2} - C.m{2} then trndL else C.v{2}.[i{2}]].[i{2}]) = true <=> true by smt. by simplify. smt.   

    while{2} ((={glob A, real, p} /\
          query{1} = query_ind{2} /\ C.n{2} <= G.g{2} <= C.n{2} + C.q{2} /\
          DKCSecurity.bound = C.n{1} + C.q{1} /\
          DKCSecurity.l = Top.l /\
          l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
          GSch.EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
        (forall (i1 : int),
          C.n{2} <= i1 < C.n{2} + C.q{2} =>
          C.v{2}.[i1] =
          oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\ 
        (forall (k : int),
          0 <= k < C.n{1} + C.q{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
          R.t{2}.[l] = !DKCp.lsb{2} /\
       (forall (k : int),
          0 <= k < C.n{1} + C.q{1} =>
          R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, C.v{1}.[k])]) /\
        (forall (k : int),
          0 <= k < C.n{1} + C.q{1} =>
          R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !C.v{1}.[k])]) /\

        (forall k, 0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, C.v{1}.[k])] <> None) /\
        (forall k, 0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, !C.v{1}.[k])] <> None) /\
        
        (forall k, 0 <= k < C.n{2} + C.q{2} => R.xx{1}.[(k,C.v{1}.[k])] = R.xx{2}.[(k,C.v{2}.[k])]) /\
        (forall k, 0 <= k < C.n{2} + C.q{2} => R.xx{1}.[(k,!C.v{1}.[k])] = R.xx{2}.[(k,!C.v{2}.[k])]))
      (C.n{2} + C.q{2} - G.g{2}).

        progress. 
        case (C.aa.[G.g] = l).
        rcondt 3. by auto. 
        rcondf 5. call (_:true) => //. call (_:true) => //. auto; progress => /#.
        wp. inline*. 
        rcondt 17. by auto.
        rcondt 32. by auto.
        cfold 3. cfold 3. cfold 3.
        cfold 15. cfold 15. cfold 15.
        auto. progress. 
          by idtac=>/#.
          by idtac=>/#.

          rewrite ?getP ?xor_true ?xor_false //=. case (k = G.g{hr}) => hk. rewrite ?hk //=. cut ->: G.g{hr} = C.bb{hr}.[G.g{hr}] <=> false by idtac=>/#. simplify. case (C.v{hr}.[G.g{hr}] = C.v{hr}.[G.g{hr}] ^^ (C.v{hr}.[G.g{hr}] ^^ oget C.gg{hr}.[(G.g{hr}, ! C.v{hr}.[C.aa{hr}.[G.g{hr}]], ! C.v{hr}.[C.bb{hr}.[G.g{hr}]])])) => hv. rewrite -hv. rewrite -some_oget. idtac=>/#. idtac=>/#. case (C.v{hr}.[G.g{hr}] = C.v{hr}.[G.g{hr}] ^^ (C.v{hr}.[G.g{hr}] ^^ oget C.gg{hr}.[(G.g{hr}, ! C.v{hr}.[C.aa{hr}.[G.g{hr}]], C.v{hr}.[C.bb{hr}.[G.g{hr}]])])) => hv'. rewrite -hv'. rewrite -some_oget. idtac=>/#. idtac=>/#. idtac=>/#. simplify. case (k = C.bb{hr}.[G.g{hr}]) => hk'. rewrite ?hk' //=. cut ->: C.v{hr}.[C.bb{hr}.[G.g{hr}]] = ! C.v{hr}.[C.bb{hr}.[G.g{hr}]] <=> false by idtac=>/#. simplify. rewrite -some_oget. idtac=>/#. idtac=>/#. simplify. idtac=>/#.

          rewrite ?getP ?xor_true ?xor_false //=. case (k = G.g{hr}) => hk. rewrite ?hk //=. cut ->: G.g{hr} = C.bb{hr}.[G.g{hr}] <=> false by idtac=>/#. simplify. case ((!C.v{hr}.[G.g{hr}]) = C.v{hr}.[G.g{hr}] ^^ (C.v{hr}.[G.g{hr}] ^^ oget C.gg{hr}.[(G.g{hr}, ! C.v{hr}.[C.aa{hr}.[G.g{hr}]], ! C.v{hr}.[C.bb{hr}.[G.g{hr}]])])) => hv. rewrite -hv. rewrite -some_oget. idtac=>/#. idtac=>/#. case ((!C.v{hr}.[G.g{hr}]) = C.v{hr}.[G.g{hr}] ^^ (C.v{hr}.[G.g{hr}] ^^ oget C.gg{hr}.[(G.g{hr}, ! C.v{hr}.[C.aa{hr}.[G.g{hr}]], C.v{hr}.[C.bb{hr}.[G.g{hr}]])])) => hv'. rewrite -hv'. rewrite -some_oget. idtac=>/#. idtac=>/#. idtac=>/#. simplify. case (k = C.bb{hr}.[G.g{hr}]) => hk'. rewrite ?hk' //=. idtac=>/#. simplify. idtac=>/#. 

         by idtac=>/#.    
         by idtac=>/#. 
         by idtac=>/#. 
         by idtac=>/#.
         by idtac=>/#.
         by idtac=>/#.      

       case (C.bb.[G.g] = l).
         rcondf 3. by auto.
         rcondt 3. by auto.
         wp. inline*.
         rcondf 16. by auto.
         rcondf 31. by auto.
         cfold 3. cfold 3. cfold 3.
         cfold 15. cfold 15. cfold 15.
         auto. progress. 
           by idtac=>/#.
           by idtac=>/#.
           
           rewrite ?getP ?xor_true ?xor_false //=. case (k = G.g{hr}) => hk. rewrite ?hk //=. cut ->: G.g{hr} = C.aa{hr}.[G.g{hr}] <=> false by idtac=>/#. simplify. case (C.v{hr}.[G.g{hr}] = C.v{hr}.[G.g{hr}] ^^ (C.v{hr}.[G.g{hr}] ^^ oget C.gg{hr}.[(G.g{hr}, C.v{hr}.[C.aa{hr}.[G.g{hr}]], ! C.v{hr}.[C.bb{hr}.[G.g{hr}]])])) => hv. rewrite -hv. rewrite -some_oget. idtac=>/#. idtac=>/#. idtac=>/#. case (k = C.aa{hr}.[G.g{hr}]) => hk'. rewrite ?hk' //=. cut ->: C.v{hr}.[C.aa{hr}.[G.g{hr}]] = ! C.v{hr}.[C.aa{hr}.[G.g{hr}]] <=> false by idtac=>/#. simplify. rewrite -some_oget. idtac=>/#. idtac=>/#. simplify. idtac=>/#.

          rewrite ?getP ?xor_true ?xor_false //=. case (k = C.aa{hr}.[G.g{hr}]) => hk. rewrite ?hk //=. idtac=>/#. simplify. case (k = G.g{hr}) => hk'. rewrite ?hk' //=. case ((!C.v{hr}.[G.g{hr}]) = C.v{hr}.[G.g{hr}] ^^ (C.v{hr}.[G.g{hr}] ^^ oget C.gg{hr}.[(G.g{hr}, C.v{hr}.[C.aa{hr}.[G.g{hr}]], ! C.v{hr}.[C.bb{hr}.[G.g{hr}]])])) => hv. idtac=>/#. idtac=>/#. simplify. idtac=>/#.

          by idtac=>/#.    

        rcondf 3. by auto.
        rcondf 3. by auto.

        auto. progress.

          by idtac=>/#.
          by idtac=>/#.
          by idtac=>/#.
      
    wp.

      

      ((={glob A, real, p} /\
          query{1} = query_ind{2} /\
        DKCSecurity.bound = C.n{1} + C.q{1} /\
        DKCSecurity.l = Top.l /\
          l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
        (GSch.EncSecurity.queryValid_IND query{1}) /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
        (forall (i1 : int),
          C.n{2} <= i1 < C.n{2} + C.q{2} =>
          C.v{2}.[i1] =
          oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])])
        
        ==>

        ((={glob A, real, p} /\
    query{1} = query_ind{2} /\
    C.n{2} <= C.n{2} <= C.n{2} + C.q{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    DKCSecurity.l = Top.l /\
    l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
   (GSch.EncSecurity.queryValid_IND query{1}) /\
   (C.v{1}, C.gg{1}, C.bb{1}, C.aa{1}, C.q{1}, C.m{1}, C.n{1}, C.x{1}, C.f{1}) =
   (C.v{2}, C.gg{2}, C.bb{2}, C.aa{2}, C.q{2}, C.m{2}, C.n{2}, C.x{2}, C.f{2}) /\
   size C.v{1} = C.n{1} + C.q{1} /\
   C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
   validInputsP (C.f{1}, C.x{1}) /\
   (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
   (forall (i1 : int),
      C.n{2} <= i1 < C.n{2} + C.q{2} =>
      C.v{2}.[i1] =
      oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
   (forall (k : int),
      0 <= k < C.n{1} + C.q{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
   R.t{2}.[Top.l] = !DKCp.lsb{2} /\
   (forall (k : int),
      0 <= k < C.n{1} + C.q{1} =>
      R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, C.v{1}.[k])]) /\
   (forall (k : int),
      0 <= k < C.n{1} + C.q{1} =>
      R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! C.v{1}.[k])]) /\
   (forall (k : int),
      0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, C.v{1}.[k])] <> None) /\
   (forall (k : int),
      0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, ! C.v{1}.[k])] <> None) /\
   (forall (k : int),
      0 <= k < C.n{2} + C.q{2} =>
      R.xx{1}.[(k, C.v{1}.[k])] = R.xx{2}.[(k, C.v{2}.[k])]) /\
   forall (k : int),
     0 <= k < C.n{2} + C.q{2} =>
     R.xx{1}.[(k, ! C.v{1}.[k])] = R.xx{2}.[(k, ! C.v{2}.[k])]) /\
  forall (xx_R : tokens_t) (g_R : int),
    ((={glob A, real, p} /\
      query{1} = query_ind{2} /\
      C.n{2} <= g_R <= C.n{2} + C.q{2} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\
      l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     (C.v{1}, C.gg{1}, C.bb{1}, C.aa{1}, C.q{1}, C.m{1}, C.n{1}, C.x{1},
      C.f{1}) =
     (C.v{2}, C.gg{2}, C.bb{2}, C.aa{2}, C.q{2}, C.m{2}, C.n{2}, C.x{2},
      C.f{2}) /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
     R.t{2}.[Top.l] = !DKCp.lsb{2} /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, C.v{1}.[k])]) /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! C.v{1}.[k])]) /\
     (forall (k : int),
        0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, C.v{1}.[k])] <> None) /\
     (forall (k : int),
        0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, ! C.v{1}.[k])] <> None) /\
     (forall (k : int),
        0 <= k < C.n{2} + C.q{2} =>
        R.xx{1}.[(k, C.v{1}.[k])] = xx_R.[(k, C.v{2}.[k])]) /\
     forall (k : int),
       0 <= k < C.n{2} + C.q{2} =>
       R.xx{1}.[(k, ! C.v{1}.[k])] = xx_R.[(k, ! C.v{2}.[k])] =>
     C.n{2} + C.q{2} - g_R <= 0 => ! g_R < C.n{2} + C.q{2}) /\
    (! g_R < C.n{2} + C.q{2} =>
     (={glob A, real, p} /\
      query{1} = query_ind{2} /\
      C.n{2} <= g_R <= C.n{2} + C.q{2} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      DKCSecurity.l = Top.l /\
      l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     (C.v{1}, C.gg{1}, C.bb{1}, C.aa{1}, C.q{1}, C.m{1}, C.n{1}, C.x{1},
      C.f{1}) =
     (C.v{2}, C.gg{2}, C.bb{2}, C.aa{2}, C.q{2}, C.m{2}, C.n{2}, C.x{2},
      C.f{2}) /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} => k <> Top.l => R.t{1}.[k] = R.t{2}.[k]) /\
     R.t{2}.[Top.l] = !DKCp.lsb{2} /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, C.v{1}.[k])]) /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! C.v{1}.[k])]) /\
     (forall (k : int),
        0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, C.v{1}.[k])] <> None) /\
     (forall (k : int),
        0 <= k < C.n{2} + C.q{2} => DKCp.kpub{2}.[(k, ! C.v{1}.[k])] <> None) /\
     (forall (k : int),
        0 <= k < C.n{2} + C.q{2} =>
        R.xx{1}.[(k, C.v{1}.[k])] = xx_R.[(k, C.v{2}.[k])]) /\
     forall (k : int),
       0 <= k < C.n{2} + C.q{2} =>
       R.xx{1}.[(k, ! C.v{1}.[k])] = xx_R.[(k, ! C.v{2}.[k])] =>
     ={glob A, real, p} /\
     query{1} = query_ind{2} /\
     DKCSecurity.bound = C.n{1} + C.q{1} /\
     DKCSecurity.l = Top.l /\
     l{1} = Top.l /\
     !DKCp.b{2} /\
     !b{2} /\
     DKCp.b{2} = b{2} /\
     (GSch.EncSecurity.queryValid_IND query{1}) /\
     (C.v{1}, C.gg{1}, C.bb{1}, C.aa{1}, C.q{1}, C.m{1}, C.n{1}, C.x{1},
      C.f{1}) =
     (C.v{2}, C.gg{2}, C.bb{2}, C.aa{2}, C.q{2}, C.m{2}, C.n{2}, C.x{2},
      C.f{2}) /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i0_0 : int),
        0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
     (forall (i0_0 : int),
        C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
        C.v{2}.[i0_0] =
        oget
          C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
     (forall (k : int), 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < C.n{1} + C.q{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = xx_R.[(k, C.v{2}.[k])]) /\
     forall (k : int),
       0 <= k < C.n{1} + C.q{1} =>
       R.xx{1}.[(k, ! C.v{1}.[k])] = xx_R.[(k, ! C.v{2}.[k])])
      )
      (
        true ==> true
        ). 

        admit. admit.

      swap{2} 10 -4. swap{2} 11 -5. 
        
      while ((={glob A, real, p, i, useVisible} /\ useVisible{1} /\
            query{1} = query_ind{2} /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
            DKCSecurity.bound = C.n{1} + C.q{1} /\
            DKCSecurity.l = Top.l /\
            l{1} = Top.l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2}) /\
          (GSch.EncSecurity.queryValid_IND query{1}) /\
          ={glob C} /\
            size C.v{1} = C.n{1} + C.q{1} /\
            C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
            validInputsP (C.f{1}, C.x{1}) /\
          (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
          (forall (i1 : int),
            C.n{2} <= i1 < C.n{2} + C.q{2} =>
            C.v{2}.[i1] =
            oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
          (forall k, 0 <= k < i{1} => R.xx{1}.[(k,C.v{1}.[k])] = DKCp.kpub{2}.[(k,C.v{2}.[k])]) /\
          (forall k, 0 <= k < i{1} => R.xx{1}.[(k,!C.v{1}.[k])] = DKCp.kpub{2}.[(k,!C.v{2}.[k])])).

      wp. swap{2} 5 -4. rnd{2}. rnd{2}. rnd. rnd. wp. rnd. skip. progress.
        smt. smt. smt. smt. smt. idtac=>/#. idtac=>/#. 
        rewrite ?getP H //=. case (k = i{2}) => hk. rewrite ?hk //=. case (C.v{2}.[i{2}] = false) => hv. cut ->: C.v{2}.[i{2}] = ! C.v{2}.[i{2}] <=> false by idtac=>/#. rewrite hv //=. cut ->: C.v{2}.[i{2}] = ! C.v{2}.[i{2}] <=> false by idtac=>/#. simplify. cut ->: C.v{2}.[i{2}] = true <=> true by idtac=>/#. simplify. idtac=>/#. cut ->: 

        
        progress. auto; progress.
          


        case (R.xx.[(i0, ! C.v.[i0])] = None /\ i0 <> Top.l).
          rcondt 1; first by auto.
          case (R.xx.[(i0, C.v.[i0])] = None).
            rcondt 2; first by auto; smt.
          wp; skip. progress. 
      
        auto. progress. smt.

      
      
qed.



lemma GameHybrid_l1_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
      ={glob A} /\ l = DKCSec2.l /\ l{1} = l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} ==> ={res}].
proof.
  move => Agen_ll Aget_ll.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  swap{2} 10 -9.
  seq 1 1 : (={glob A}, l{1} = Top.l - 1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2})




  seq 1 10 : (={glob A} /\ l{1} = l - 1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\ query{1} = query_ind{2} /\ DKCp.kpub{2} = map0 /\ DKCp.used{2} = fset0 /\ DKCp.rr{2} = map0 /\ lsb{2} = DKCp.lsb{2} /\ 0 <= l < SomeGarble.bound /\ lsb{2} = DKCp.lsb{2} /\ ).
    by call (_ : true) => //; auto; progress; first 3 by smt.

  if; first by progress.
    wp; call (_ : true) => //; wp.
    call HybridInitEq_Adv. 
    call RandomInitEq_Adv.
    call CircuitInitEquiv.
    wp; rnd; skip; progress.
      by move : H3; rewrite /validInputsP /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP /fst /snd; case realL => /#. 
      by rewrite fmapP => x; elim x => k a b => /#.
      simplify encode. congr. rewrite fun_ext /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hx. case (mem (dom xx_L) (x, x_R.[x])) => hxx. cut ? : xx_L.[(x, x_R.[x])] <> None by rewrite -in_dom. cut ? : xx_R.[(x, x_R.[x])] <> None by rewrite -H9 => /#. cut ->: mem (dom xx_R) (x, x_R.[x]) <=> true by rewrite in_dom. simplify. by rewrite -H9 => /#. cut ? : xx_L.[(x, x_R.[x])] = None by smt. cut ? : xx_R.[(x, x_R.[x])] = None by rewrite -H9 => /#. cut ->: mem (dom xx_R) (x, x_R.[x]) <=> false by smt. by simplify. by simplify.
      by rewrite H => /#.
  by auto => /#. 
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
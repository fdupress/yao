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
  proc query (rn : bool, alpha : bool, betha : bool) : word = {
    var twe : word;
    var gamma, pos : bool;
    var i,j : int;
    var ki, kj, zz : word;

    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ betha);
    gamma = C.v.[G.g] ^^ oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ betha)];

    pos = if G.a = l then true else false;
    i = if G.a = l then 2*G.b + bti (R.t.[G.b] ^^ betha) else 2*G.a + bti (R.t.[G.a] ^^ alpha);
    j = $[2*(G.g + C.n + C.q) .. 2*(G.g + C.n + C.q)+1];
    j = if rn then j else 2*(G.g + C.n + C.q);

    (ki,kj,zz) = D.encrypt((i,j,pos,twe));

    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ betha)] = zz;
    
    if (G.a = l) {
      R.xx.[(G.b, C.v.[G.b] ^^ betha)] = ki;
    }
    else {
      R.xx.[(G.a, C.v.[G.a] ^^ alpha)] = ki;
    }

    if (!rn) {
      R.xx.[(G.g, C.v.[G.g] ^^ gamma)] = kj;
    }

    return kj;
  }

  proc init(useVisible:bool): unit = {
    var tok1, tok2, v, trnd, i;
      
    R.t = offun (fun x, false) (C.n + C.q);
    R.xx = map0;

    i = 0;
    while (i < C.n + C.q) {
      trnd = ${0,1};
      v = if useVisible then C.v.[i] else false;
      trnd = if (i < C.n + C.q - C.m) then trnd else v;
      tok1 = $Dword.dwordLsb ( trnd);
      tok2 = $Dword.dwordLsb (!trnd);

      R.t.[i] = trnd;

      R.xx.[(i, v)] = tok1;
      R.xx.[(i,!v)] = tok2;
      
      i = i + 1;
    }
    
    G.g = C.n;
    while (G.g < C.n + C.q) {

      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
      R.t.[l] = DKCp.lsb;

      if (G.a = l) {
        query(false,true,false);
        query(false,true,true);
      }

      if (G.b = l) {
        query(false,false,true);
        G.yy.[G.g] = query(true,true,true);
      }
      
      G.g = G.g + 1;
    }
  }
}.
  
lemma RandomInitEq_Adv:
  equiv [RandomInit.init ~ AdvRandomInit(DKC).init :
  ={glob C} /\ size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f, C.x){1} /\
  useVisible{1}  ==>
    size R.t{1} = size R.t{2} /\
    (size R.t = C.n + C.q){1} /\
    ={R.t} /\
    (R.t.[l] = !DKCp.lsb){2} /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = R.xx{2}.[(k, C.v{2}.[k])]) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = R.xx{2}.[(k, !C.v{2}.[k])]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*C.bb{2}.[k] + bti (R.t{2}.[C.bb{2}.[k]])] = R.xx{2}.[(C.bb{2}.[k], C.v{2}.[C.bb{2}.[k]])]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*C.bb{2}.[k] + bti (!R.t{2}.[C.bb{2}.[k]])] = R.xx{2}.[(C.bb{2}.[k], !C.v{2}.[C.bb{2}.[k]])]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*k + bti (R.t{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], C.v{2}.[C.bb{2}.[k]])]))] = R.xx{2}.[(k, C.v{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], C.v{2}.[C.bb{2}.[k]])]))]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*k + bti (R.t{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))] = R.xx{2}.[(k, C.v{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.bb{2}.[k] = l => DKCp.kpub{2}.[2*C.aa{2}.[k] + bti (R.t{2}.[C.aa{2}.[k]])] = R.xx{2}.[(C.aa{2}.[k], C.v{2}.[C.aa{2}.[k]])]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.bb{2}.[k] = l => DKCp.kpub{2}.[2*C.aa{2}.[k] + bti (!R.t{2}.[C.aa{2}.[k]])] = R.xx{2}.[(C.aa{2}.[k], !C.v{2}.[C.aa{2}.[k]])]) /\
    (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.bb{2}.[k] = l => DKCp.kpub{2}.[2*k + bti (R.t{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))] = R.xx{2}.[(k, C.v{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))])].
proof. admit. qed.
  
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

lemma HybridInitEq_Adv:
  equiv [GarbleHybridInit.init ~ AdvInit(DKC).init :
  ={glob C} /\ size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f, C.x){1} /\
  size R.t{1} = size R.t{2} /\
  (size R.t = C.n + C.q){1} /\
  ={R.t} /\
  (R.t.[l] = !DKCp.lsb){2} /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = R.xx{2}.[(k, C.v{2}.[k])]) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => k <> l => R.xx{1}.[(k, !C.v{1}.[k])] = R.xx{2}.[(k, !C.v{2}.[k])]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*C.bb{2}.[k] + bti (R.t{2}.[C.bb{2}.[k]])] = R.xx{2}.[(C.bb{2}.[k], C.v{2}.[C.bb{2}.[k]])]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*C.bb{2}.[k] + bti (!R.t{2}.[C.bb{2}.[k]])] = R.xx{2}.[(C.bb{2}.[k], !C.v{2}.[C.bb{2}.[k]])]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*k + bti (R.t{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], C.v{2}.[C.bb{2}.[k]])]))] = R.xx{2}.[(k, C.v{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], C.v{2}.[C.bb{2}.[k]])]))]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.aa{2}.[k] = l => DKCp.kpub{2}.[2*k + bti (R.t{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))] = R.xx{2}.[(k, C.v{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, !C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.bb{2}.[k] = l => DKCp.kpub{2}.[2*C.aa{2}.[k] + bti (R.t{2}.[C.aa{2}.[k]])] = R.xx{2}.[(C.aa{2}.[k], C.v{2}.[C.aa{2}.[k]])]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.bb{2}.[k] = l => DKCp.kpub{2}.[2*C.aa{2}.[k] + bti (!R.t{2}.[C.aa{2}.[k]])] = R.xx{2}.[(C.aa{2}.[k], !C.v{2}.[C.aa{2}.[k]])]) /\
  (forall k, C.n{2} <= k < C.n{2} + C.q{2} => C.bb{2}.[k] = l => DKCp.kpub{2}.[2*k + bti (R.t{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))] = R.xx{2}.[(k, C.v{2}.[k] ^^ (C.v{2}.[k] ^^ oget C.gg{2}.[(k, C.v{2}.[C.aa{2}.[k]], !C.v{2}.[C.bb{2}.[k]])]))]) ==>

    (forall k a b, C.n{1} <= k < C.n{1} + C.q{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
    (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
    (forall k a b, C.n{1} + C.q{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
    (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
    (forall k a b, C.n{1} + C.q{1} <= k => G.pp{2}.[(k,a,b)] = None)].
proof. admit. qed.

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

lemma GameHybrid_l1_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
      ={glob A} /\ l{1} = l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} ==> ={res}].
proof.
  move => Agen_ll Aget_ll.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  seq 1 7 : (={glob A} /\ l{1} = l - 1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\ query{1} = query_ind{2} /\ DKCp.kpub{2} = map0 /\ DKCp.used{2} = fset0 /\ DKCp.rr{2} = map0 /\ lsb{2} = DKCp.lsb{2} /\ 0 <= l < SomeGarble.bound).
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

lemma GameHybrid_l_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ l{1} = l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} ==> res{1} = !res{2}].
proof.
  move => Agen_ll Aget_ll.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  seq 1 7 : (={glob A} /\ l{1} = l /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\ query{1} = query_ind{2} /\ DKCp.kpub{2} = map0 /\ DKCp.used{2} = fset0 /\ DKCp.rr{2} = map0 /\ lsb{2} = DKCp.lsb{2} /\ 0 <= l < SomeGarble.bound).
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
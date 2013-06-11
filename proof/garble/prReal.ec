require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Bool.
require import Array.
require import Logic.
require import Real.
require import Distr.
require import MyRand.

require import MyDkc.
require import GarbleTools.
require import Garble.
require import AdvGarbleAda.

(*STRANGE VEHAVIOUR :
module type Ty = {}.

  module M(A:Ty, B:Ty) = {
fun f() : unit = {}
}.


  module G(A:Ty, B:Ty) = {

    module C = M(A, B)

fun f() : unit = {C.f();}
  }.

theory T.
module X : Ty = {}.
end T.

equiv test : G(T.X, T.X).f ~ G(T.X, T.X).f : true ==> true.
fun.
inline M(T.X,T.X).f.
inline G(T.X, T.X).C.f.
*)

module RandGarble2 : Rand_t = {
  fun gen(f:funct, x:input) : random = {
    var i : int;
    var g : int;
    var a : int;
    var b : int;
    var t:bool array;
    var v : bool;
    var xx : tokens;
    var tok : token;
    var n : int;
    var m : int;
    var q : int;
    var aa : w2g;
    var bb : w2g;
    var gg : bool g2v;
    (n, m, q, aa, bb, gg) = f;

    i = 0;
    while (i < n+q-m-1) {
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < (getN f)+(getQ f)-1) {
      t.[i] = false;
      i = i + 1;
    }

    g = n;
    while (g < n+q-1) {
      a = aa.[g];
      b = bb.[g];
      if (a = 0) {
        v = ! (eval f x i);
        
        tok = $DKC.genRandKeyLast (t.[b]);
        xx = setTok xx g false tok;

        tok = $DKC.genRandKeyLast (evalGate gg.[g] (v,false));
        xx = setTok xx g (evalGate gg.[g] (v,false)) tok;

        tok = $DKC.genRandKeyLast (!t.[b]);
        xx = setTok xx g true tok;

        tok = $DKC.genRandKeyLast (evalGate gg.[g] (v,true));
        xx = setTok xx g (evalGate gg.[g] (v,true)) tok;
      }
      g = g + 1;
    }

    i = 0;
    while (i < n+q-1) {
      if (getTok xx i true = void /\ i <> 0) {
        tok = $DKC.genRandKeyLast (! t.[i]);
        xx = setTok xx i true tok;
      }
      if (getTok xx i false = void) {
        tok = $DKC.genRandKeyLast (t.[i]);
        xx = setTok xx i false tok;
      }
      i = i + 1;
    }
    return xx;
  }
}.


lemma realEq :
  forall (ADV <: Garble.Adv{AdvAda, DKC.Dkc}),
    equiv [
      GameAda(DKC.Dkc, ADV).work ~
      Garble.Game(Garble.PrvInd(RandGarble2), ADV).main
      : (glob ADV){1} = (glob ADV){2} /\
      (DKC.Dkc.b{1}) /\ (AdvAda.l{1}=0) ==> res{1} = res{2}
    ].
proof.

  intros ADV.
  fun.
  inline {1} GameAda(DKC.Dkc, ADV).A.work.
  inline {1} AdvAda(ADV, DKC.Dkc).work.
  inline {1} AdvAda(ADV, DKC.Dkc).garble.
  inline {1} DKC.Dkc.preInit.
  inline {1} DKC.Dkc.get_challenge.
  inline {1} DKC.Dkc.initialize.
  inline {1} DKC.Dkc.encrypt.
  inline {1} AdvAda(ADV, DKC.Dkc).query.
  inline {1} AdvAda(ADV, DKC.Dkc).garb.
  inline {1} AdvAda(ADV, DKC.Dkc).garbD.
  inline {2} Garble.PrvInd(RandGarble2).garb.
  inline {2} Garble.PrvInd(RandGarble2).get_challenge.
  inline {2} RandGarble2.gen.

  swap{1} 7 -6.

  app 1 1 : (AdvAda.query{1} = query{2}/\DKC.Dkc.b{1}).
    call ((glob ADV){1} = (glob ADV){2}) (res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2}).
      fun true;trivial.
  skip;trivial.
  
  case (Garble.queryValid query{2}).

  (*VALID*)
  rcondt {1} 18;[intros _;wp;rnd;wp;rnd;rnd;skip;trivial|].
  rcondt {2} 1;[intros &m;skip;trivial|].
  wp.
  call ((glob ADV){1} = (glob ADV){2}/\answer{1}=answer{2}) (res{1}=res{2});[fun true;trivial|].
  wp.
  app 26 15 : (
    (glob ADV){1} = (glob ADV){2} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2}
  ).
  wp.
  app 24 13 : (
    (glob ADV){1} = (glob ADV){2} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2}
  ).
  
  admit.
  while (
    (glob ADV){1} = (glob ADV){2} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    AdvAda.xc{1} = x{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.i{1} = i{2}
  ).
  wp.
  app 1 1 : (
    (glob ADV){1} = (glob ADV){2} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    AdvAda.xc{1} = x{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.i{1} = i{2}
  );(if;[progress|wp;rnd;skip;progress|skip;progress]).
  wp;skip;progress.
  
  app 2 0 : (
    (glob ADV){1} = (glob ADV){2} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    AdvAda.xc{1} = x{2}/\
    let (g, e, d) = garble xx{2} f{2} in getG g = AdvAda.pp{1}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}).
    admit. (*While one sided*)
  skip.
  delta garble.
  progress. trivial.

  (*INVALID*)
  rcondf {1} 18;[intros _;wp;rnd;wp;rnd;rnd;skip;trivial|].
  rcondf {1} 26. admit.
  rcondf {2} 1;[intros &m;skip;trivial|].
  wp.
  rnd.
  kill{1} 1!25.
  skip;trivial.
    admit.
save.

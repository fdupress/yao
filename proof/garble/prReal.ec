require import Bitstring.
require import List.
require import Map.
require import Set.
require import Pair.
require import Int.
require import Bool.
require import Array.
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
    var t0 : bool;
    var xx : tokens;
    var tok : token;
    var n : int;
    var m : int;
    var q : int;
    var aa : w2g;
    var bb : w2g;
    var gg : bool g2v;
    var dkckey : token;
    (n, m, q, aa, bb, gg) = f;
    t = Array.init (n+q) false;
    xx = Array.init (n+q) (void, void);

    t0 = $Dbool.dbool;
    v = x.[0];
    dkckey = $DKC.genRandKeyLast (t0);

    i = 0;
    while (i < n+q-m) {
      t.[i] = $Dbool.dbool;
      i = i + 1;
    }
    while (i < n+q) {
      t.[i] = false;
      i = i + 1;
    }

    t.[0] = !t0;


    g = n;
    while (g < n+q) {
      a = aa.[g];
      b = bb.[g];
      if (a = 0) {
        v = ! (eval f x i);
        
        if (getTok xx b false = void)
        {
          tok = $DKC.genRandKeyLast (t.[b]);
          xx = setTok xx b false tok;
        }

        tok = $DKC.genRandKeyLast (evalGate gg.[g] (!v,false));
        xx = setTok xx g (evalGate gg.[g] (!v,false)) tok;

        if (getTok xx b true = void)
        {
          tok = $DKC.genRandKeyLast (!t.[b]);
          xx = setTok xx b true tok;
        }

        tok = $DKC.genRandKeyLast (evalGate gg.[g] (!v,true));
        xx = setTok xx g (evalGate gg.[g] (!v,true)) tok;
      }
      g = g + 1;
    }

    i = 0;
    while (i < n+q) {
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
    xx = setTok xx 0 (!v) dkckey;
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
  inline {1} AdvAda(ADV, DKC.Dkc).query.
  inline {1} AdvAda(ADV, DKC.Dkc).garb.
  inline {1} AdvAda(ADV, DKC.Dkc).garbD.
  inline {1} DKC.Dkc.preInit.
  inline {1} DKC.Dkc.get_challenge.
  inline {1} DKC.Dkc.initialize.
  inline {1} DKC.Dkc.encrypt.
  inline {2} Garble.PrvInd(RandGarble2).garb.
  inline {2} Garble.PrvInd(RandGarble2).get_challenge.
  inline {2} RandGarble2.gen.

  swap{1} 7 -6.

  seq 1 1 : ((glob ADV){1} = (glob ADV){2}/\AdvAda.query{1} = query{2}/\DKC.Dkc.b{1} /\ (AdvAda.l{1}=0)).
    call ((glob ADV){1} = (glob ADV){2}) (res{1}=res{2} /\ (glob ADV){1} = (glob ADV){2});first (fun true;by progress).
  skip;progress;assumption.
  
  case (Garble.queryValid query{2}).

  (*VALID*)
  rcondt {1} 18;first (intros _;wp;rnd;wp;rnd;rnd;skip;progress assumption).
  rcondt {2} 1;first (intros &m;skip;by progress).
  wp.
  call ((glob ADV){1} = (glob ADV){2}/\answer{1}=answer{2}) (res{1}=res{2});first (fun true;by progress).
  wp.
  seq 26 19 : (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
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
  );first last.
  admit. (*ONE SIDED WHILE*)

  wp.

  seq 23 17 : (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
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
  );first last.

  while (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
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
    AdvAda.i{1} = i{2}/\
    0 <= i{2}
  ).
    wp.
    seq 1 1 : (
      (glob ADV){1} = (glob ADV){2} /\
      length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
      length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
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
      AdvAda.i{1} = i{2} /\
      0 <= i{2} /\
      i{2} < n{2} + q{2}
    );(if;[|wp;rnd;skip|skip];progress assumption;trivial).

  wp.

  skip;progress assumption;trivial.

  seq 21 15 : (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.l{1} = 0 /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < i /\ aa{2}.[i] < bb{2}.[i]) /\
    validfx (f{2},x{2})
  );first last.



  while (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.g{1} = g0{2} /\
    AdvAda.l{1} = 0 /\
    n{2} <= g0{2} /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < i /\ aa{2}.[i] < bb{2}.[i]) /\
    validfx (f{2},x{2}) /\
    (forall g a b, g >= g0{2} => !(mem (tweak g a b) DKC.Dkc.used{1}))
  ).
  wp.
  seq 2 2 : (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.l{1} = 0 /\
    AdvAda.a{1} = a{2} /\
    n{2} <= g0{2} /\
    g0{2} < n{2} + q{2} /\
    AdvAda.g{1} = g0{2} /\
    AdvAda.b{1} = b{2} /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < i /\ aa{2}.[i] < bb{2}.[i]) /\
    (a{2} < b{2}) /\
    (0 <= a{2})/\
    (b{2} < g0{2}) /\
    validfx (f{2},x{2}) /\
    (forall g a b, g >= g0{2} => !(mem (tweak g a b) DKC.Dkc.used{1}))
  );first (wp;skip;progress assumption;trivial).
  seq 1 1 : (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.l{1} = 0 /\
    AdvAda.a{1} = a{2} /\
    n{2} <= g0{2} /\
    g0{2} < n{2} + q{2} /\
    AdvAda.g{1} = g0{2} /\
    AdvAda.b{1} = b{2} /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < i /\ aa{2}.[i] < bb{2}.[i]) /\
    (b{2} < g0{2}) /\
    (a{2} < b{2}) /\
    (0 <= a{2}) /\
    validfx (f{2},x{2}) /\
    b{2} <> 0 /\
    (forall g a b, g >= g0{2} => !(mem (tweak g a b) DKC.Dkc.used{1}))
  );last (rcondf{1} 1;first (intros _);skip;trivial).
  if;first (progress assumption).
  wp.
  rcondt{1} 11;first (intros _;rcondt 6;last (rcondf 8);wp;skip;trivial).
  rcondt{1} 34.
  intros _.
  wp.
  kill 12!12;first admit.
  rcondt 6;last (rcondf 8);[wp;skip;trivial|wp;skip;trivial|].
  rcondt 18;last (rcondf 20);wp;skip.
  trivial.
  trivial.
  progress.
  trivial.
  admit.
  skip;progress assumption;trivial.

  wp.
  skip;progress assumption;trivial.

  wp.

  seq 17 11 : (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.l{1} = 0 /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < n{2} + q{2} - m{2} /\ aa{2}.[i] < bb{2}.[i]) /\
    validfx (f{2},x{2}) /\
    AdvAda.tau{1} = t0{2}
  );first last.    

  while (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.l{1} = 0 /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < n{2} + q{2} - m{2} /\ aa{2}.[i] < bb{2}.[i]) /\
    validfx (f{2},x{2}) /\
    AdvAda.i{1} = i{2} /\
    0 <= i{2}
  );first (wp;skip;progress assumption;trivial).

  while (
    (glob ADV){1} = (glob ADV){2} /\
    length AdvAda.xx{1} = AdvAda.n{1}+AdvAda.q{1} /\
    length AdvAda.t{1} = AdvAda.n{1}+AdvAda.q{1} /\
    AdvAda.xx{1} = xx{2} /\
    AdvAda.t{1} = t{2}/\
    AdvAda.n{1} = n{2}/\
    AdvAda.m{1} = m{2}/\
    AdvAda.q{1} = q{2}/\
    AdvAda.aa{1} = aa{2}/\
    AdvAda.bb{1} = bb{2}/\
    AdvAda.fc{1} = f{2}/\
    (AdvAda.c{1} = DKC.Dkc.b{1}) = PrvInd.b{2}/\
    AdvAda.xc{1} = x{2} /\
    AdvAda.l{1} = 0 /\
    f{2} = (n{2}, m{2}, q{2}, aa{2}, bb{2}, gg{2}) /\
    (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < n{2} + q{2} - m{2} /\ aa{2}.[i] < bb{2}.[i]) /\
    validfx (f{2},x{2}) /\
    AdvAda.i{1} = i{2} /\
    0 <= i{2}
  );first (wp;rnd;wp;skip;progress assumption;trivial).

  wp.

  skip;progress assumption;trivial.

  swap{1} 7 -6.
  wp.
  rnd.
  wp.
  rnd.
  wp.
  rnd (lambda x, x = DKC.Dkc.b{1}) _.
  wp.

  skip.

  intros &1 &2 h c b.
  elim h;clear h;intros h h1.
  elim h;clear h;intros h2 h;
  elim h;clear h;intros h3 h4.
  simplify.
  split;first trivial.
  intros h5 h6.
  case (c).
    intros hypeq.
    simplify.
    cut bval : (DKC.Dkc.b{1} = true);first trivial.
    rewrite bval.
    simplify.
    elimT tuple6_ind (fst (fst query{2})).
    intros n m q aa bb gg hf1.
    simplify.
    intros t ht ksec hksec.
    rewrite h3.
    rewrite hf1.
    simplify.
    split;first assumption.
    split;first trivial.
    split;first trivial.
    split;first trivial.
    cut lem : (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < n{2} + q{2} - m{2} /\ aa{2}.[i] < bb{2}.[i]).
      apply (valid_wireinput ((n{2},m{2},q{2},aa{2},bb{2},gg{2}), snd (fst query{2})) _);trivial.
    split;[assumption|trivial].

    intros hypeq.
    simplify.
    cut bval : (DKC.Dkc.b{1} = true);first trivial.
    rewrite bval.
    simplify.
    elimT tuple6_ind (fst (snd query{2})).
    intros n m q aa bb gg hf1.
    simplify.
    intros t ht ksec hksec.
    rewrite h3.
    rewrite hf1.
    simplify.
    split;first assumption.
    split;first trivial.
    split;first trivial.
    split;first trivial.
    cut lem : (forall i, i >= n{2} => i < n{2}+q{2} => aa{2}.[i] >= 0 /\
           bb{2}.[i] < n{2} + q{2} - m{2} /\ aa{2}.[i] < bb{2}.[i]).
      apply (valid_wireinput ((n{2},m{2},q{2},aa{2},bb{2},gg{2}), snd (snd query{2})) _);trivial.
    split;[assumption|trivial].

  (*INVALID*)
  rcondf {1} 18;first (intros _;wp;rnd;wp;rnd;rnd;skip;trivial).
  rcondf {2} 1;[intros &m;skip;trivial|].
  wp.
  rnd.
  kill{1} 1!17;first (wp;rnd 1%r cPtrue;wp;rnd 1%r cPtrue;rnd 1%r cPtrue;skip;progress;trivial).
  skip;trivial.
save.

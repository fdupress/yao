require import Array.
require import Map.
require import Pair.
require import Int.
require import Bool.

require import GarbleTools.
require import PreProof.

(* This is the circuit to garble (fixed after the adversary runs and the challenge is chosen) *)
module C = {
  var f:funct
  var x:input
  var n:int
  var m:int
  var q:int
  var aa:w2g
  var bb:w2g
  var gg:bool g2v
  var v:bool array
  
  fun init(p:PrvIndSec.Scheme.plain) : unit = {
    var i : int;
    f = fst p;
    x = snd p;
    n = getN f;
    m = getM f;
    q = getQ f;
    aa = getA f;
    bb = getB f;
    gg = getG f;
    v = Array.create (C.n + C.q) false;
    i = 0;
    while (i < n + q) {
      v.[i] = eval f x i;
      i = i + 1;
    }
  }
}.

lemma CinitL: bd_hoare[C.init: true ==> true] = 1%r by (fun;(while true (C.n + C.q - i);first intros z);wp;skip;smt).
lemma CinitH : forall (plain:PrvIndSec.Scheme.plain), functCorrect (fst plain) =>
  hoare[C.init: p=plain ==>
    C.f = fst plain /\ C.x = snd plain /\ (C.n, C.m, C.q, C.aa, C.bb, C.gg) = fst plain /\ Array.length C.v = (C.n+C.q) /\ functCorrect C.f]
  by (intros _ _;fun;while (Array.length C.v = (C.n+C.q));wp;skip;smt).
lemma CinitE : equiv[C.init ~ C.init : ={p} ==> ={glob C}]
  by (fun;while (={glob C, i});wp;skip;smt).



(*Contains the random used for a normal garbling*)
module R = {
  var t:bool array
  var xx:tokens

  fun init(useVisible:bool) : unit = {
    var i : int;
    var tok1, tok2 : token;
    var v, trnd : bool;
    t = Array.create (C.n + C.q) false;
    xx = Array.create (C.n + C.q) (void, void);
    i = 0;
    while (i < C.n + C.q) {
      trnd = $Dbool.dbool;
      tok1 = $Dkc.DKC.genRandKeyLast;
      tok2 = $Dkc.DKC.genRandKeyLast;
      v = if useVisible then C.v.[i] else false;
      t.[i] = if (i >= C.n + C.q - C.m) then false^^v else trnd;
      xx = setTok xx i (false^^v) (Dkc.DKC.addLast tok1 ( t.[i]));
      xx = setTok xx i ( true^^v) (Dkc.DKC.addLast tok2 (!t.[i]));
      i = i + 1;
    }
  }
}.

lemma RgenInitL: bd_hoare[R.init: true ==> true] = 1%r
  by (fun;while true (C.n + C.q - i);[intros z;wp;do 3 ! rnd;skip;smt|wp];skip;smt).

lemma RinitH: hoare[R.init: 0 <= C.m <= C.n + C.q ==>
  tokenCorrect C.n C.q C.m R.xx /\
  Array.length R.xx = (C.n+C.q) /\
  Array.length R.t = (C.n+C.q)].
fun.
(while (0 <= C.m <= C.n + C.q /\
  Array.length R.xx = (C.n+C.q) /\
  Array.length R.t = (C.n+C.q) /\
  (forall (j:int), 0 <= j => j < i =>
    (Dkc.DKC.lsb (getTok R.xx j false)) <> (Dkc.DKC.lsb (getTok R.xx j true))) /\
  (forall (j:int), C.n + C.q - C.m <= j => j < i =>
    !(Dkc.DKC.lsb (getTok R.xx j false)) ) /\
  Array.length R.xx = (C.n+C.q) /\
  Array.length R.t = (C.n+C.q)
  );wp;first do 3 ! rnd);skip;progress assumption;rewrite ? set_get_tok ? length_setTok;smt.
save.

lemma RinitE: equiv[R.init ~ R.init : ={useVisible, glob C} ==> ={glob R}]
  by (fun;(while (={useVisible, glob R, i});wp;first do 3 ! rnd)).

pred t_xor (sup:int) (t1 t2 v:bool array) = (forall i, 0 <= i < sup => t1.[i] = t2.[i] ^^ v.[i]).

lemma RgenClassicVisibleE: equiv[R.init ~ R.init : 0 <= C.n{2} + C.q{2} /\ ={glob C} /\ useVisible{1} = true /\ useVisible{2} = false ==> t_xor (C.n{1} + C.q{1}) R.t{1} R.t{2} C.v{1} /\ ={R.xx}].
fun.
while (={i, R.xx, glob C} /\ useVisible{1} = true /\ useVisible{2} = false /\ t_xor i{1} R.t{1} R.t{2} C.v{1} /\ 0 <= i{2} /\ length R.t{1} = C.n{2} + C.q{2} /\ length R.t{2} = C.n{2} + C.q{2} /\ length R.xx{2} = C.n{2} + C.q{2}).
case (C.v{1}.[i{1}] = false).
  wp;rnd;rnd;wp;rnd;skip;((progress assumption;first smt);first simplify t_xor;progress;cut := H i0;smt);smt.
  wp;swap{1} 2 1.
rnd;rnd;wp;rnd (lambda x, !x);skip.
    progress assumption.
smt.
smt.
rewrite set_tokC;smt.
simplify t_xor;progress;cut := H i0;smt.
smt.
smt.
smt.
smt.
wp.
skip.
smt.
save.

module type Flag_t = { fun gen() : unit }.

module G = {
  var pp:token g2v
  var yy:token array
  var randG: (int*bool*bool,token) map
  var a:int
  var b:int
  var g:int

  fun garb(yy:token, alpha:bool, bet:bool) : unit = {
    pp.[g] = setGateVal pp.[g] ((R.t.[a]^^alpha), (R.t.[b]^^bet)) (Dkc.DKC.E
      (tweak g (R.t.[a]^^alpha) (R.t.[b]^^bet))
      (getTok R.xx a alpha)
      (getTok R.xx b bet)
      yy);
  }

  fun garbD1(rand:bool, alpha:bool, bet:bool) : unit = {
    var tok : token;
    tok = $DKC.genRandKey;
    if (rand) randG.[(g,alpha,bet)] = tok;
  }

  fun garbD2(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;
    if (rand)
      yy = proj randG.[(g,alpha,bet)];
    else
      yy = getTok R.xx g (evalGate C.gg.[g] ((C.v.[a]^^alpha),(C.v.[b]^^alpha)));
    garb(yy, alpha, bet);
    return yy;
  }

  fun garbD(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;
    garbD1(rand, alpha, bet);
    yy = garbD2(rand, alpha, bet);
    return yy;
  }
}.

lemma GgarbL   : bd_hoare[G.garb  : true ==> true] = 1%r by (fun;wp).
lemma GgarbD1L : bd_hoare[G.garbD1: true ==> true] = 1%r by (fun;wp;rnd;skip;smt).
lemma GgarbD2L : bd_hoare[G.garbD2: true ==> true] = 1%r by (fun;call GgarbL;wp).
lemma GgarbDL  : bd_hoare[G.garbD : true ==> true] = 1%r by (fun;call GgarbD2L;call GgarbD1L).

lemma GgarbE   : equiv[G.garb   ~ G.garb  : ={glob G, glob C, glob R, yy, alpha, bet} ==> ={glob G, glob C, glob R}]
  by (fun;wp).
lemma GgarbD1E : equiv[G.garbD1 ~ G.garbD1: ={glob G, glob C, glob R, rand, alpha, bet} ==> ={glob G, glob C, glob R}]
  by (fun;wp;rnd;skip;smt).
lemma GgarbD2E : equiv[G.garbD2 ~ G.garbD2: ={glob G, glob C, glob R, rand, alpha, bet} ==> ={glob G, glob C, glob R, res}]
  by (fun;call GgarbE;wp).
lemma GgarbDE  : equiv[G.garbD  ~ G.garbD : ={glob G, glob C, glob R, rand, alpha, bet} ==> ={glob G, glob C, glob R, res}]
  by (fun;call GgarbD2E;call GgarbD1E).

module F = {
  var flag_ff : bool
  var flag_ft : bool
  var flag_tf : bool
  var flag_tt : bool
  var flag_sp : bool
}.
 
module GInit(Flag:Flag_t) = {
  fun init() : unit = {
    var tok : token;
    G.yy = Array.create (C.n + C.q) void;
    G.pp = Array.create (C.n + C.q) (void, void, void, void);
    G.randG = Map.empty;
    G.g = C.n;
    G.a = 0;
    G.b = 0;
    while (G.g < C.n + C.q)
    {
      Flag.gen();
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
      tok = G.garbD(F.flag_ff, false, false);
      tok = G.garbD(F.flag_ft, false,  true);
      tok = G.garbD(F.flag_tf,  true, false);
      G.yy.[G.g] = G.garbD(F.flag_tt,  true,  true);
      if (F.flag_sp) G.garb(G.yy.[G.g], true, false);
      G.g = G.g + 1;
    }
  }
}.

lemma GinitL (F<:Flag_t): islossless F.gen => bd_hoare[GInit(F).init: true ==> true] = 1%r by admit.

op todo = true. (*Need to find condition necessary for profing equality of flag
           aa.[i] >= 0 /\
           bb.[i] < i /\
           bb.[i] < n+q-m /\
           aa.[i] < bb.[i] 
*)

lemma GinitE (F1<:Flag_t) (F2<:Flag_t):
  equiv[F1.gen ~ F2.gen : todo /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ] =>
    equiv[GInit(F1).init ~ GInit(F2).init : ={glob C, glob R} ==> ={glob G}] by admit.
(*  by (intros h;fun;(while (={glob G, glob C, glob R});last by wp);wp;seq 7 7 : (={glob G, glob C, glob R, glob F});[
    do 4 ! call GgarbDE;wp;call h|
    if;[|call GgarbE|]
  ]).*)


module Garble1 : GC.PrvIndSec.Scheme_t = {
  fun enc(p:GC.PrvIndSec.Scheme.plain) : GC.PrvIndSec.Scheme.cipher = {
    C.init(p);
    R.init(false);
    return
      let (g, ki, ko) = garble R.xx C.f in
      (g, encrypt ki C.x, ko);
  }
}.

module Garble2(F:Flag_t) : GC.PrvIndSec.Scheme_t = {
  module GI = GInit(F)
  fun enc(p:GC.PrvIndSec.Scheme.plain) : GC.PrvIndSec.Scheme.cipher = {
    var tok1, tok2 : token;
    C.init(p);
    R.init(true);
    GI.init();
    return (
      (C.n, C.m, C.q, C.aa, C.bb, G.pp),
      encrypt (Array.sub R.xx 0 C.n) C.x,
      tt);
  }
}.

pred qCorrect p = PrvInd_Circuit.Garble.inputCorrect (fst p) (snd p) /\ PrvInd_Circuit.Garble.functCorrect (fst p).

lemma Garble2E (F1<:Flag_t) (F2<:Flag_t):
  equiv[F1.gen ~ F2.gen : todo /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ] =>
    equiv[Garble2(F1).enc ~ Garble2(F2).enc : ={p} /\ qCorrect p{1} ==> ={res}] by admit.

module FR : Flag_t = {
  fun gen() : unit = {
    F.flag_ff = false;
    F.flag_ft = false;
    F.flag_tf = false;
    F.flag_tt = false;
    F.flag_sp = false;
  }
}.
lemma FReal_genL : bd_hoare[FR.gen  : true ==> true] = 1%r by (fun;wp).

module FF : Flag_t = {
  fun gen() : unit = {
    F.flag_ff = false;
    F.flag_ft = true;
    F.flag_tf = true;
    F.flag_tt = true;
    F.flag_sp = false;
  }
}.
lemma FFake_genL : bd_hoare[FF.gen  : true ==> true] = 1%r by (fun;wp).

module FH : Flag_t = {
  var l : int
  fun gen() : unit = {
    F.flag_ff = false;
    F.flag_ft = G.a <= l;
    F.flag_tf = G.b <= l;
    F.flag_tt = G.a <= l;
    F.flag_sp = G.a <= l < G.b /\ (evalGate C.gg.[G.g] ((!C.v.[G.a]), false) = evalGate C.gg.[G.g] ((!C.v.[G.a]), true));
  }
}.
lemma FHybrid_genL : bd_hoare[FH.gen  : true ==> true] = 1%r by (fun;wp).

lemma equiv_FH_FR :
  equiv[FH.gen ~ FR.gen : todo /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ] by admit.

lemma equiv_FH_FF :
  equiv[FH.gen ~ FF.gen : todo /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ] by admit.

lemma equivGReal : equiv[Garble2(FH).enc ~ Garble2(FR).enc : ={p} /\ qCorrect p{1} ==> ={res}]
  by (apply (Garble2E FH FR);apply equiv_FH_FR).

lemma equivGarble1 : equiv[Garble1.enc ~ Garble2(FR).enc : ={p} /\ qCorrect p{1} ==> ={res}]
  by admit.

lemma equivGFake : equiv[Garble2(FH).enc ~ Garble2(FF).enc : ={p} /\ qCorrect p{1} ==> ={res}]
  by (apply (Garble2E FH FF);apply equiv_FH_FF).

lemma equivPrvInd (A<:GC.PrvIndSec.Adv_t) (S1<:GC.PrvIndSec.Scheme_t) (S2<:GC.PrvIndSec.Scheme_t) :
  equiv[ S1.enc ~ S2.enc : ={p} /\ qCorrect p{1} ==> ={res}] =>
    equiv[ GC.PrvIndSec.Game(S1, A).main ~ PrvIndSec.Game(S2, A).main : true ==> ={res}]
  by (intros hS;fun;
    (seq 1 1 : (={query, glob A});first by call (_ : true ==> ={res, glob A});[fun true|skip;progress;assumption]);
    (if=> //;last by rnd);
    wp;(call (_ : ={cipher, glob A} ==> ={res})=> //;first by fun true);call hS;wp;rnd;skip;smt).

module Hybrid(A:PrvIndSec.Adv_t) = {
  module PrvInd = GC.PrvIndSec.Game(Garble2(FH), A)
  fun main(l:int) : bool = {
    var b : bool;
    FH.l = l;
    b = PrvInd.main();
    return b;
  }
}.

module PrvInd(A:PrvIndSec.Adv_t) = {
  module PrvInd = PrvIndSec.Game(Garble1, A)
  fun main() : bool = {
    var b : bool;
    b = PrvInd.main();
    return b;
  }
}.

lemma equivFake (A<:GC.PrvIndSec.Adv_t) :
  equiv[ GC.PrvIndSec.Game(Garble2(FH), A).main ~ PrvIndSec.Game(Garble2(FF), A).main : true ==> ={res}]
  by (apply (equivPrvInd A (Garble2(FH)) (Garble2(FF)));apply (equivGFake)).



require import FSet.
require import Monoid.
require import Real.


lemma prReal (A<:GC.PrvIndSec.Adv_t) &m:
  Pr[Hybrid(A).main(0)@ &m :res] = Pr[PrvIndSec.Game(Garble1, A).main()@ &m :res].
  cut h : equiv[GC.PrvIndSec.Game(Garble2(FH), A).main~PrvIndSec.Game(Garble1, A).main:FH.l{1} = 0 ==> ={res}];
    last admit. (*Feature request or idea*)
  admit.  (* Need to propagate the l condition *)
  (*
  apply (equivPrvInd A (Garble2(FH)) (Garble1)). (* Why it does not work directly ? *)
bypr (res{1}) (res{2})=> //.
progress.
cut -> : Pr[Garble1.enc(p0) @ &m2 : a = res] = Pr[Garble2(FR).enc(p0) @ &m2 : a = res]
  by (equiv_deno equivGarble1=> //;admit). (* BUG easycrypt ??? *)
equiv_deno equivGReal=> //;admit. (* BUG easycrypt ??? *) *)
save.

lemma prFake (A<:GC.PrvIndSec.Adv_t) &m:
  Pr[Hybrid(A).main(Cst.bound)@ &m:res] = 1%r / 2%r
  by admit.

lemma reduction :
  forall (A<:PrvIndSec.Adv_t),
    islossless A.gen_query =>
    islossless A.get_challenge =>
    exists (D<:DKCS.Adv_t),
      forall &m,
        Mrplus.sum (lambda l, Pr[Hybrid(A).main(l) @ &m : res]) (Interval.interval 1 Cst.bound) -
        Mrplus.sum (lambda l, let l = l-1 in 1%r - Pr[Hybrid(A).main(l) @ &m : res]) (Interval.interval 1 Cst.bound) =
        2%r * Cst.bound%r * Pr[DKCS.Game(DKCS.Dkc, D).main()@ &m:res] by admit. (*reduction proof*)

lemma reductionSimplified :
  forall (A<:PrvIndSec.Adv_t),
    islossless A.gen_query =>
    islossless A.get_challenge =>
    exists (D<:DKCS.Adv_t),
      forall &m,
        Pr[Hybrid(A).main(0) @ &m : res] - Pr[Hybrid(A).main(Cst.bound) @ &m : res] =
        2%r * (Cst.bound+1)%r * (Pr[DKCS.Game(DKCS.Dkc, D).main()@ &m:res] - 1%r / 2%r) by admit. (*Sum simplification*)

lemma _PrvIndDkc :
  forall (ADVG<:PrvIndSec.Adv_t),
    islossless ADVG.gen_query =>
    islossless ADVG.get_challenge =>
    exists (ADVD<:DKCS.Adv_t),
      forall &m,
        `|Pr[PrvIndSec.Game(Garble1, ADVG).main()@ &m:res] - 1%r / 2%r| =
           2%r * (Cst.bound+1)%r * `|Pr[DKCS.Game(DKCS.Dkc, ADVD).main()@ &m:res] - 1%r / 2%r|.
proof strict.
  intros A ? ?.
  elim (reductionSimplified A _ _)=> //.
  intros D red_temp.
  exists D.
  intros &m.
  rewrite -(prReal A &m).
  rewrite -{1}(prFake A &m).
  cut := red_temp &m=> /= ->.
  cut -> : forall (a b:real), a >= 0%r => `| a * b | = a * `| b | by smt;smt.
save.
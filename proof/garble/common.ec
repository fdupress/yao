require import Array.
require import Map.
require import Pair.
require import Int.
require import Bool.
require import FSet.
require import Monoid.
require import Real.

require import GarbleTools.
require import PreProof.

(* This modules contains values set at the beginning and are not modified *)
module CV = {
  var l : int
}.

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
}.

module Cf = {
  fun init(p:PrvIndSec.Scheme.plain) : unit = {
    var i : int;
    C.f = fst p;
    C.x = snd p;
    C.n = getN C.f;
    C.m = getM C.f;
    C.q = getQ C.f;
    C.aa = getA C.f;
    C.bb = getB C.f;
    C.gg = getG C.f;
    C.v = Array.create (C.n + C.q) false;
    i = 0;
    while (i < C.n + C.q) {
      C.v.[i] = eval C.f C.x i;
      i = i + 1;
    }
  }
}.

lemma CinitL: bd_hoare[Cf.init: true ==> true] = 1%r.
proof strict.
by fun; while true (C.n + C.q - i); [intros z | ];
   wp; skip; smt.
qed.

lemma CinitH (plain:PrvIndSec.Scheme.plain):
  functCorrect (fst plain) =>
  hoare[Cf.init: p = plain ==>
                C.f = fst plain /\
                C.x = snd plain /\
                (C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.f /\
                Array.length C.v = (C.n + C.q) /\
                functCorrect C.f].
proof strict.
by intros=> fCor; fun;
   while (Array.length C.v = C.n + C.q); wp; skip; smt.
qed.

equiv CinitE: Cf.init ~ Cf.init: ={p} /\ (functCorrect (fst p)){1}==> ={glob C} /\
                ((C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.f /\
                Array.length C.v = (C.n + C.q) /\
                functCorrect C.f){1}.
proof strict.
fun; while ((Array.length C.v = C.n + C.q){1} /\ ={glob C, i}); wp; skip.
progress assumption.
smt.
simplify functCorrect validCircuit getN getQ.
intros &1 &2 [h ].
elimT tuple6_ind (fst p{2}).
intros n m q aa bb gg.
subst.
intros ->.
progress assumption;smt.
qed.

lemma fst : forall (x y:'a), fst (x, y) = x by smt.
lemma snd : forall (x y:'a), snd (x, y) = y by smt.

equiv CinitE_rnd: Cf.init ~ Cf.init:
PrvIndSec.Scheme.queryValid (p{1}, p{2})
==> ={C.n, C.m, C.q, C.aa, C.bb} /\
                (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i]) /\
                ((C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.f /\
                Array.length C.v = (C.n + C.q) /\
                functCorrect C.f /\
                inputCorrect C.f C.x){1} /\
                ((C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.f /\
                Array.length C.v = (C.n + C.q) /\
                functCorrect C.f /\
                inputCorrect C.f C.x){2} /\
                (GarbleCircuit.eval C.f C.x){1} = (GarbleCircuit.eval C.f C.x){2} /\
                (forall i, 0 <= i < C.n{1} => C.v{1}.[i] = C.x{1}.[i]) /\
                (forall i, 0 <= i < C.n{1} => C.v{2}.[i] = C.x{2}.[i]).
proof strict.
fun; while (0 <= C.q{2} /\ 0 <= C.n{2} + C.q{2} - C.m{2} /\ (Array.length C.v = C.n + C.q){2} /\ (Array.length C.v = C.n + C.q){1} /\ ={C.n, C.m, C.q, C.aa, C.bb, i} /\
                (GarbleCircuit.eval C.f C.x){1} = (GarbleCircuit.eval C.f C.x){2} /\ (forall j, C.n{1} + C.q{1} - C.m{1} <= j < i{1} => C.v{1}.[j] = C.v{2}.[j]) /\
                ((C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.f){2} /\
                ((C.n, C.m, C.q, C.aa, C.bb, C.gg) = C.f){1} /\ (C.n = length C.x){1} /\ (C.n = length C.x){2} /\
                (forall j, 0 <= j < i{1} /\ j < C.n{1} => C.v{1}.[j] = C.x{1}.[j]) /\
                (forall j, 0 <= j < i{1} /\ j < C.n{1}=> C.v{2}.[j] = C.x{2}.[j])); wp; skip.
progress assumption.
smt.
smt.
rewrite ! set_get;first 4 smt.
case (i{2} = j);last smt.
cut : ((sub
  (evalComplete (length C.x{1}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}, C.gg{1}) C.x{1}
     extract) (length C.x{1} + C.q{2} - C.m{2}) C.m{2}).[i{2} - (length C.x{1} + C.q{2} - C.m{2})] =
(sub
  (evalComplete (length C.x{1}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}, C.gg{2}) C.x{2}
     extract) (length C.x{1} + C.q{2} - C.m{2}) C.m{2}).[i{2} - (length C.x{1} + C.q{2} - C.m{2})]) by smt.
rewrite ! sub_get;first 10 smt.
smt.

rewrite set_get;first 2 smt.
case (i{2} = j)=> h;last smt.
simplify GarbleTools.eval GarbleTools.evalComplete.
rewrite MyTools.appendInit_get1;smt.

rewrite set_get;first 2 smt.
case (i{2} = j)=> h;last smt.
simplify GarbleTools.eval GarbleTools.evalComplete.
rewrite MyTools.appendInit_get1;smt.

simplify PrvIndSec.Scheme.queryValid PrvInd_Circuit.Scheme.queryValid functCorrect validCircuit getN getQ.
intros &1 &2.
rewrite !fst !snd.
elimT tuple6_ind (fst p{2}).
elimT tuple6_ind (fst p{1}).
progress assumption;smt.
qed.

(*Contains the random used for a normal garbling *)
module R = {
  var t:bool array
  var xx:tokens
}.

module Rf = {
  fun init(useVisible:bool): unit = {
    var i:int;
    var tok1,tok2:token;
    var v,trnd:bool;

    R.t = Array.create (C.n + C.q) false;
    R.xx = Array.create (C.n + C.q) (void, void);
    i = 0;
    while (i < C.n + C.q) {
      trnd = $Dbool.dbool;
      tok1 = $Dkc.DKC.genRandKeyLast;
      tok2 = $Dkc.DKC.genRandKeyLast;

      v = if useVisible then C.v.[i] else false;
      R.t.[i] = if (i >= C.n + C.q - C.m) then false ^^ v else trnd;

      R.xx = setTok R.xx i (false^^v) (Dkc.DKC.addLast tok1 ( R.t.[i]));
      R.xx = setTok R.xx i ( true^^v) (Dkc.DKC.addLast tok2 (!R.t.[i]));

      i = i + 1;
    }
  }
}.

lemma RgenInitL: bd_hoare[Rf.init: true ==> true] = 1%r.
proof strict.
by fun; while true (C.n + C.q - i); [intros=> z; wp; do 3!rnd | wp];
   skip; smt.
qed.

lemma RinitH:
  hoare[Rf.init: 0 <= C.m <= C.n + C.q ==>
                tokenCorrect C.n C.q C.m R.xx /\
                Array.length R.xx = (C.n+C.q) /\
                Array.length R.t = (C.n+C.q)].
proof strict.
fun; while (0 <= C.m <= C.n + C.q /\
            Array.length R.xx = C.n + C.q /\
            Array.length R.t = C.n + C.q /\
            (forall (j:int), 0 <= j => j < i =>
              Dkc.DKC.lsb (getTok R.xx j false) <> Dkc.DKC.lsb (getTok R.xx j true)) /\
            (forall (j:int), C.n + C.q - C.m <= j => j < i =>
              !Dkc.DKC.lsb (getTok R.xx j false)));
  first by wp; do 3!rnd; skip; progress=> //;
           rewrite ?set_get_tok ?length_setTok; smt.
by wp; skip; smt.
qed.

equiv RinitE: Rf.init ~ Rf.init: ={useVisible, glob C}  /\ (0 <= C.m <= C.n + C.q){1} ==> ={glob R} /\
                (tokenCorrect C.n C.q C.m R.xx /\
                Array.length R.xx = (C.n+C.q) /\
                Array.length R.t = (C.n+C.q)){1}.
proof strict.
by fun; while (={useVisible, glob C, glob R, i} /\ (
            0 <= C.m <= C.n + C.q /\
            Array.length R.xx = C.n + C.q /\
            Array.length R.t = C.n + C.q /\
            (forall (j:int), 0 <= j => j < i =>
              Dkc.DKC.lsb (getTok R.xx j false) <> Dkc.DKC.lsb (getTok R.xx j true)) /\
            (forall (j:int), C.n + C.q - C.m <= j => j < i =>
              !Dkc.DKC.lsb (getTok R.xx j false))){1}); [wp; do 3!rnd | wp];skip;progress assumption;rewrite ?set_get_tok ?length_setTok;smt.
qed.

equiv RinitE_rnd: Rf.init ~ Rf.init:
(0 < C.m <= C.n + C.q /\ useVisible = true){1} /\
={useVisible, C.n, C.m, C.q, C.aa, C.bb} /\
(forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i])
==>
(0 <= C.m <= C.n + C.q /\ tokenCorrect C.n C.q C.m R.xx /\ Array.length R.xx = (C.n+C.q) /\ Array.length R.t = (C.n+C.q)){1} /\
length R.xx{1} = length R.xx{2} /\
={R.t} /\
(forall x g, 0 <= g < (C.n + C.q){1} => (getTok R.xx g (x^^C.v.[g])){1} = (getTok R.xx g (x^^C.v.[g])){2}
).
fun; while (
(
  0 <= C.m <= C.n + C.q /\
  Array.length R.xx = C.n + C.q /\
  Array.length R.t = C.n + C.q /\
  (forall (j:int), 0 <= j => j < i => Dkc.DKC.lsb (getTok R.xx j false) <> Dkc.DKC.lsb (getTok R.xx j true)) /\
  (forall (j:int), C.n + C.q - C.m <= j => j < i => !Dkc.DKC.lsb (getTok R.xx j false)) /\
  length R.xx = C.n+C.q /\
  useVisible = true
){1} /\
={useVisible, C.n, C.m, C.q, C.aa, C.bb, R.t, i} /\
(forall x g, 0 <= g < i{1} => (getTok R.xx g (x^^C.v.[g])){1} = (getTok R.xx g (x^^C.v.[g])){2}) /\
length R.xx{1} = length R.xx{2} /\
(forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i]) /\ useVisible{1} = true

);last (wp;skip;progress assumption).
wp.
(case (C.v{1}.[i{1}]=C.v{2}.[i{1}]);last swap 2 1);rnd;rnd;rnd;skip;progress assumption;rewrite ? set_get_tok ? length_setTok;try smt.
case (i{2}=g);smt.
timeout 10.
case (i{2}=g);case x;smt.
timeout 2.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
qed.

pred t_xor (sup:int) (t1 t2 v:bool array) = forall i,
  0 <= i < sup =>
  t1.[i] = t2.[i] ^^ v.[i].

equiv RgenClassicVisibleE:
  Rf.init ~ Rf.init:
    ={glob C} /\
    0 <= C.n{2} + C.q{2} /\
    useVisible{1} = true /\
    useVisible{2} = false ==>
    ={R.xx} /\
    t_xor (C.n{1} + C.q{1}) R.t{1} R.t{2} C.v{1}.
proof strict.
fun; while (={i, R.xx, glob C} /\
            useVisible{1} = true /\
            useVisible{2} = false /\
            t_xor i{1} R.t{1} R.t{2} C.v{1} /\
            0 <= i{2} /\
            length R.t{1} = C.n{2} + C.q{2} /\
            length R.t{2} = C.n{2} + C.q{2} /\
            length R.xx{2} = C.n{2} + C.q{2}).
  case (C.v{1}.[i{1}] = false).
    by do !(wp; rnd); skip; progress=> //;
       rewrite /t_xor //=; progress=> //; try (cut := H i0); smt.
    swap{1} 2 1; do 2!(wp; rnd); rnd (lambda x, !x); skip; progress=> //;
      last 4 smt.
      smt.
      smt.
      by (rewrite set_tokC;first 3 smt);congr=> //;smt.
      by simplify t_xor; progress; cut:= H i0; smt.
by wp; skip; smt.
qed.

(*(forall g, 0 <= g < (C.n + C.q){1} => (getTok R.xx g C.v.[g]){1} = (getTok R.xx g C.v.[g]){2}  )*)

module type G_t = {
  fun getInfo() : int*int*bool
}.

(* handle low level part of garbling *)
module G = {
  var pp:token g2v
  var yy:token array
  var randG: (int*bool*bool,token) map
  var a:int
  var b:int
  var g:int
}.

module Gf : G_t = {
  fun garb(yy:token, alpha:bool, bet:bool): unit = {
    G.pp.[G.g] =
      setGateVal G.pp.[G.g] ((R.t.[G.a]^^alpha), (R.t.[G.b]^^bet))
                 (Dkc.DKC.E
                   (tweak G.g (R.t.[G.a]^^alpha) (R.t.[G.b]^^bet))
                   (getTok R.xx G.a (alpha^^C.v.[G.a]))
                   (getTok R.xx G.b (bet  ^^C.v.[G.b]))
                   yy);
  }

  fun garbD1(rand:bool, alpha:bool, bet:bool): unit = {
    var tok:token;

    tok = $DKC.genRandKey;
    if (rand) G.randG.[(G.g,alpha,bet)] = tok;
  }

  fun garbD2(rand:bool, alpha:bool, bet:bool) : token = {
    var yy:token;

    yy = if (rand)
         then proj G.randG.[(G.g,alpha,bet)]
         else getTok R.xx G.g (evalGate C.gg.[G.g] ((C.v.[G.a]^^alpha),(C.v.[G.b]^^alpha)));
    garb(yy, alpha, bet);
    return yy;
  }

  fun garbD(rand:bool, alpha:bool, bet:bool) : token = {
    var yy : token;

    garbD1(rand, alpha, bet);
    yy = garbD2(rand, alpha, bet);
    return yy;
  }

  fun getInfo() : int*int*bool = {
    return (G.a, G.b, (evalGate C.gg.[G.g] ((!C.v.[G.a]), false) = evalGate C.gg.[G.g] ((!C.v.[G.a]), true)));
  }
}.

lemma GgarbL    : islossless Gf.garb    by (fun; wp).

lemma GgarbD1L  : islossless Gf.garbD1  by (fun; wp; rnd; skip; smt).

lemma GgarbD2L  : islossless Gf.garbD2  by (fun; call GgarbL; wp).

lemma GgarbDL   : islossless Gf.garbD   by (fun; call GgarbD2L; call GgarbD1L).

lemma GgetInfoL : islossless Gf.getInfo by (fun;wp).

equiv GgarbE   : Gf.garb   ~ Gf.garb   : (getTok R.xx G.a (alpha^^C.v.[G.a])){1} = (getTok R.xx G.a (alpha^^C.v.[G.a])){2} /\ (getTok R.xx G.b (bet^^C.v.[G.b])){1} = (getTok R.xx G.b (bet^^C.v.[G.b])){2} /\ ={glob G, C.n, C.m, C.q, C.aa, C.bb, R.t,   yy, alpha, bet} ==> ={glob G, res}
  by (fun;wp;skip;smt).

equiv GgarbD1E : Gf.garbD1 ~ Gf.garbD1 : ={glob G, C.n, C.m, C.q, C.aa, C.bb, rand, alpha, bet} ==> ={glob G, res}
  by (fun;wp;rnd;skip;smt).

equiv GgarbD2E : Gf.garbD2 ~ Gf.garbD2 : ={glob G, glob C, glob R, rand, alpha, bet} ==> ={glob G, res}
  by (fun;call GgarbE;wp).

equiv GgarbD2E_rnd : Gf.garbD2 ~ Gf.garbD2 : (getTok R.xx G.a (alpha^^C.v.[G.a])){1} = (getTok R.xx G.a (alpha^^C.v.[G.a])){2} /\ (getTok R.xx G.b (bet^^C.v.[G.b])){1} = (getTok R.xx G.b (bet^^C.v.[G.b])){2} /\ rand{1}=true /\ ={glob G, C.n, C.m, C.q, C.aa, C.bb, R.t, rand, alpha, bet} ==> ={glob G, res}
  by (fun;call GgarbE;wp).

equiv GgarbDE  : Gf.garbD  ~ Gf.garbD  : ={glob G, glob C, glob R, rand, alpha, bet} ==> ={glob G, res}
  by (fun;call GgarbD2E;call GgarbD1E).

equiv GgarbDE_rnd  : Gf.garbD  ~ Gf.garbD  : (getTok R.xx G.a (alpha^^C.v.[G.a])){1} = (getTok R.xx G.a (alpha^^C.v.[G.a])){2} /\ (getTok R.xx G.b (bet^^C.v.[G.b])){1} = (getTok R.xx G.b (bet^^C.v.[G.b])){2} /\ rand{1}=true /\ ={glob G, C.n, C.m, C.q, C.aa, C.bb, R.t, rand, alpha, bet} ==> ={glob G, res}
  by (fun;call GgarbD2E_rnd;call GgarbD1E).

(* Contains the flag variables used by GInit, their value depends
   of the type of the garbling : Fake, Real, Hybrid *)
module F = {
  var flag_ft : bool
  var flag_tf : bool
  var flag_tt : bool
  var flag_sp : bool
}.

(* Type of a module that fill the F modules *)
module type Flag_t(G:G_t) = { fun gen() : unit{ G.getInfo } }.

(*handle high level part of garbling *)
module GInit(Flag:Flag_t) = {

  module Flag = Flag(Gf)

  fun init() : unit = {
    var tok : token;

    G.yy = Array.create (C.n + C.q) void;
    G.pp = Array.create (C.n + C.q) (void, void, void, void);
    G.randG = Map.empty;
    G.a = 0;
    G.b = 0;

    G.g = C.n;
    while (G.g < C.n + C.q)
    {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
      Flag.gen();
      Gf.garb(getTok R.xx G.g C.v.[G.g], false, false);
      tok = Gf.garbD(F.flag_ft, false,  true);
      tok = Gf.garbD(F.flag_tf,  true, false);
      G.yy.[G.g] = Gf.garbD(F.flag_tt,  true,  true);
      if (F.flag_sp) Gf.garb(G.yy.[G.g], true, false);
      G.g = G.g + 1;
    }
  }
}.

lemma GinitL (F <: Flag_t{G}): islossless F(Gf).gen => islossless GInit(F).init.
proof strict.
intros h.  
fun.
while true (C.n + C.q - G.g).
intros z.
inline Gf.garbD Gf.garbD1 Gf.garbD2 Gf.garb.
wp;do ! (rnd;wp).
call (_:true ==> true)=> //.
wp.
skip.
progress assumption;smt.
wp.
skip.
progress assumption;smt.
save.

op todo (a b g bound:int) = a >= 0 /\ b < g /\ b < Cst.bound+1 /\ a < b.

lemma GinitE (F1<:Flag_t{G}) (F2<:Flag_t{G}) gCV1:
  equiv[F1(Gf).gen ~ F2(Gf).gen :
    (glob CV){1} = gCV1 /\
    (todo G.a G.b G.g (C.n+C.q-C.m)){1} /\
    ={glob C, glob R, glob G}
  ==> ={glob C, glob R, glob G, glob F} ] =>
    equiv[GInit(F1).init ~ GInit(F2).init : (validCircuitP Cst.bound (C.n, C.m, C.q, C.aa, C.bb, C.gg)){1} /\
(glob CV){1} = gCV1 /\ ={glob C, glob R} ==> ={glob G}].
proof strict.
intros h.
fun.
(while (G.g{1} >= C.n{1} /\ (validCircuitP Cst.bound (C.n, C.m, C.q, C.aa, C.bb, C.gg)){1} /\ (glob CV){1} = gCV1 /\ ={glob G, glob C, glob R});
last by wp;skip;progress assumption;smt).
wp;seq 7 7 : (G.g{1} >= C.n{1} /\ (validCircuitP Cst.bound (C.n, C.m, C.q, C.aa, C.bb, C.gg)){1} /\ (glob CV){1} = gCV1 /\ ={F.flag_sp, glob G, glob C, glob R, glob F});[
do 3 ! call GgarbDE; call GgarbE;wp;call h;wp;skip;progress assumption;smt |
if;[|call GgarbE;skip|skip];progress assumption;smt].
save.

module Garble1 : GC.PrvIndSec.Scheme_t = {
  fun enc(p:GC.PrvIndSec.Scheme.plain) : GC.PrvIndSec.Scheme.cipher = {
    Cf.init(p);
    Rf.init(false);
    return
      let (g, ki, ko) = garble R.xx C.f in
      (g, encrypt ki C.x, ko);
  }
}.

module Garble2(F:Flag_t) : GC.PrvIndSec.Scheme_t = {
  module GI = GInit(F)
  fun enc(p:GC.PrvIndSec.Scheme.plain) : GC.PrvIndSec.Scheme.cipher = {
    var tok1, tok2 : token;
    Cf.init(p);
    Rf.init(true);
    GI.init();
    return (
      (C.n, C.m, C.q, C.aa, C.bb, G.pp),
      encrypt (Array.sub R.xx 0 C.n) C.x,
      tt);
  }
}.

pred qCorrect p = PrvInd_Circuit.Garble.inputCorrect (fst p) (snd p) /\ PrvInd_Circuit.Garble.functCorrect (fst p).

lemma Garble2E (F1<:Flag_t{G, C, R}) (F2<:Flag_t{G, C, R}) gCV1:
  equiv[F1(Gf).gen ~ F2(Gf).gen : ((glob CV){1} = gCV1) /\ (todo G.a G.b G.g (C.n+C.q-C.m)){1} /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ] =>
    equiv[Garble2(F1).enc ~ Garble2(F2).enc : ((glob CV){1} = gCV1) /\ ={p} /\ qCorrect p{1} ==> ={res}].
intros h.
fun.
call (GinitE F1 F2 gCV1 _)=> //.
call RinitE.
call CinitE.
skip.
clear h.
simplify.
rewrite /qCorrect /PrvInd_Circuit.Garble.inputCorrect /PrvInd_Circuit.Garble.functCorrect /functCorrect valid_wireinput.

intros &1 &2 [? [? [iCor fCor]]].
subst.
split;first by trivial.
intros [h1 h2] {h1 h2}.

intros _f _x _n _m _q _aa _bb _gg _v f x n m q aa bb gg v.
rewrite valid_wireinput.
intros [h [hh [lenI fCor2]]].
elim h=> {h}.
do intros ?.
subst.
split=> //.
smt.
save.

module FR(G:G_t) : Flag_t(G) = {
  fun gen() : unit = {
    F.flag_ft = false;
    F.flag_tf = false;
    F.flag_tt = false;
    F.flag_sp = false;
  }
}.
lemma FReal_genL : islossless FR(Gf).gen by (fun;wp).

module FF(G:G_t) : Flag_t(G) = {
  fun gen() : unit = {
    F.flag_ft = true;
    F.flag_tf = true;
    F.flag_tt = true;
    F.flag_sp = false;
  }
}.
lemma FFake_genL : islossless FF(Gf).gen by (fun;wp).

module FH(G:G_t) : Flag_t(G) = {
  fun gen() : unit = {
    var a, b : int;
    var val : bool;
    (a, b, val) = G.getInfo();
    
    F.flag_ft = a <= CV.l;
    F.flag_tf = b <= CV.l;
    F.flag_tt = a <= CV.l;
    F.flag_sp = a <= CV.l < b /\ val;
  }
}.

lemma FHybrid_genL : islossless FH(Gf).gen by (fun;wp;call GgetInfoL).

lemma equiv_FH_FR :
  equiv[FH(Gf).gen ~ FR(Gf).gen : ((glob CV){1} = (-1 )) /\ (todo G.a G.b G.g (C.n+C.q-C.m)){1} /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ]
   by (fun;inline Gf.getInfo;wp;skip;smt).

lemma equiv_FH_FF :
  equiv[FH(Gf).gen ~ FF(Gf).gen : ((glob CV){1} = Cst.bound) /\ (todo G.a G.b G.g (C.n+C.q-C.m)){1} /\ ={glob C, glob R, glob G} ==> ={glob C, glob R, glob G, glob F} ]
   by (fun;inline Gf.getInfo;wp;skip;smt).

lemma equivGReal : equiv[Garble2(FH).enc ~ Garble2(FR).enc : ((glob CV){1} = (-1)) /\ ={p} /\ qCorrect p{1} ==> ={res}]
  by (apply (Garble2E FH FR (-1));apply equiv_FH_FR).

lemma equivGarble1 : equiv[Garble1.enc ~ Garble2(FR).enc : ={p} /\ qCorrect p{1} ==> ={res}]
  by admit. (* TODO: main part of equivReal where logic equivalent to code *)

lemma equivGFake : equiv[Garble2(FH).enc ~ Garble2(FF).enc : ((glob CV){1} = Cst.bound){1} /\ ={p} /\ qCorrect p{1} ==> ={res}]
  by (apply (Garble2E FH FF Cst.bound);apply equiv_FH_FF).

lemma equivPrvInd (A<:GC.PrvIndSec.Adv_t{CV}) (S1<:GC.PrvIndSec.Scheme_t) (S2<:GC.PrvIndSec.Scheme_t) gCV1:
  equiv[ S1.enc ~ S2.enc : ((glob CV){1} = gCV1) /\ ={p} /\ qCorrect p{1} ==> ={res}] =>
    equiv[ GC.PrvIndSec.Game(S1, A).main ~ PrvIndSec.Game(S2, A).main : (glob CV){1} = gCV1 ==> ={res}]
  by ( (intros hS;fun;
    (seq 1 1 : ((glob CV){1} = gCV1 /\ ={query, glob A});first by call (_ : true ==> ={res, glob A});[fun true|skip;progress;assumption]);
    (if=> //;last by rnd);
    wp;(call (_ : ={cipher, glob A} ==> ={res})=> //;first by fun true);call hS;wp;rnd;skip);
    progress assumption;elim H;progress;smt).

module Hybrid(A:PrvIndSec.Adv_t) = {
  module PrvInd = GC.PrvIndSec.Game(Garble2(FH), A)
  fun main(l:int) : bool = {
    var b : bool;
    CV.l = l;
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



module GarbleFake : GC.PrvIndSec.Scheme_t = {
  module GI = GInit(FF)
  fun enc(p:GC.PrvIndSec.Scheme.plain) : GC.PrvIndSec.Scheme.cipher = {
    var tok1, tok2 : token;
    Cf.init(p);
    Rf.init(true);
    GI.init();
    return (
      (C.n, C.m, C.q, C.aa, C.bb, G.pp),
      encrypt (Array.sub R.xx 0 C.n) C.x,
      tt);
  }
}.


module Fake(A:GC.PrvIndSec.Adv_t) = {
fun main() : bool = {
var b, b', ret : bool;
var c : PrvIndSec.Scheme.cipher;
var query : (funct*input)*(funct*input);
query = A.gen_query();
if (PrvIndSec.Scheme.queryValid query) {
  b = $ {0,1};
  c = GarbleFake.enc(fst query);
  b' = A.get_challenge(c);
  ret = b = b';
} else {
  ret = $ {0,1};
}
return ret;
}
}.

lemma prFakeI (A<:GC.PrvIndSec.Adv_t) &m: islossless A.gen_query => islossless A.get_challenge =>
  Pr[Fake(A).main() @ &m:res] = 1%r / 2%r.
intros ll1 ll2.
bdhoare_deno (_: true ==> res)=> //.
fun.
seq 1 : true (1%r) (1%r/2%r) 0%r 1%r=> //;
  first call (_ : true ==> true);[fun (true)|skip];progress.
case (PrvIndSec.Scheme.queryValid query).
  (* VALID *)
  rcondt 1;first skip;progress.
  inline GarbleFake.enc.
  wp.
  swap 1 6.
  rnd (lambda b, b = b').
  call (_ : true ==> true);first fun (true);progress;assumption.
  kill 2!4;first by wp;(call (GinitL FF _);first by apply FFake_genL);call RgenInitL;call CinitL.
  wp.
  skip.
progress assumption;rewrite Dbool.mu_def /=;case (result);smt.
  (* INVALID *)
  rcondf 1;first skip;progress.
  rnd (lambda b, ! b = false).
  skip;progress;rewrite ? Dbool.mu_def //;smt.
qed.

lemma prFake (A<:GC.PrvIndSec.Adv_t{CV, G, C, R, F}) &m: islossless A.gen_query => islossless A.get_challenge =>
  Pr[PrvIndSec.Game(Garble2(FF), A).main() @ &m:res] = 1%r / 2%r.
intros ll1 ll2.
rewrite -(prFakeI A &m)=> //.  
equiv_deno (_:CV.l{1} = CV.l{m} ==> ={res}) => //.
fun.
seq 1 1 : (={query, glob A} /\ CV.l{1} = CV.l{m});
  first call (_ : true ==> ={res, glob A});[fun (true)|skip];progress.
if=> //.
wp.
call (_: ={cipher, glob A} ==> ={res});first fun true=> //.
inline Garble2(FF).enc GarbleFake.enc.
wp.
inline Garble2(FF).GI.init GarbleFake.GI.init.
(while (={glob A} /\ G.g{1} >= C.n{1} /\ (validCircuitP Cst.bound (C.n, C.m, C.q, C.aa, C.bb, C.gg)){1}  /\ ={C.n, C.m, C.q, C.aa, C.bb, glob G, R.t} /\ (forall x g, 0 <= g < (C.n + C.q){1} => (getTok R.xx g (x^^C.v.[g])){1} = (getTok R.xx g (x^^C.v.[g])){2})  )).
wp;seq 7 7 : (={glob A} /\ (G.g{1} >= C.n{1} /\ (validCircuitP Cst.bound (C.n, C.m, C.q, C.aa, C.bb, C.gg)){1}  /\ ={F.flag_sp, C.n, C.m, C.q, C.aa, C.bb, glob G, R.t} /\ (forall x g, 0 <= g < (C.n + C.q){1} => (getTok R.xx g (x^^C.v.[g])){1} = (getTok R.xx g (x^^C.v.[g])){2}) /\ 0 <= G.a{2} < C.n{2} + C.q{2} /\ 0 <= G.b{2} < C.n{2} + C.q{2} )).
do 3 ! call GgarbDE_rnd;wp;call GgarbE.
inline GInit(FF).Flag.gen.
wp.
skip.
progress assumption.
rewrite H1 //;smt.
rewrite H1 //;smt.
rewrite - (xor_false C.v{1}.[G.g{2}]) (xor_comm C.v{1}.[G.g{2}]) - (xor_false C.v{2}.[G.g{2}]) (xor_comm C.v{2}.[G.g{2}]) H1 //;smt.
rewrite H1 //.
generalize H0.
rewrite /validCircuitP.
smt.
rewrite H1 //;smt.
smt.
smt.
smt.
smt.

if.
progress assumption.
call GgarbE;skip;progress assumption;smt.
skip;progress assumption;smt.
wp.
call RinitE_rnd.
call CinitE_rnd.
wp.
rnd.
skip.

do intros ?.
split.
smt.

do intros ?.
split.
case bL;smt.

intros h.
intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? .
elimT tuple6_ind f_L.
elimT tuple6_ind f_R.
progress;try smt.
generalize H5;simplify functCorrect validCircuit;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
generalize H5;simplify functCorrect;rewrite valid_wireinput /validCircuitP;smt.
simplify encrypt choose.
(apply extensionality;split;first smt)=> len x x0 xm.
rewrite ! init_get=> // /=;first 2 smt.
cut -> :x_L.[x] = false^^v_L.[x] by smt.
cut -> :x_R.[x] = false^^v_R.[x] by smt.
cut := H27 false x _;first smt.
simplify getTok.
rewrite sub_get;first 5 smt.
rewrite sub_get.
smt.
smt.
smt.
smt.
smt.
smt.
rnd;skip;smt.
save.

lemma prH0 (A<:GC.PrvIndSec.Adv_t{CV, G, C, R, F}) &m: let ll = -1 in
  Pr[Hybrid(A).main(ll)@ &m :res] = Pr[PrvIndSec.Game(Garble1, A).main()@ &m :res].
proof strict.
intros=> ll.
equiv_deno (_: l{1} = -1 ==> ={res})=> //.
fun*;inline Hybrid(A).main.
wp;call (equivPrvInd A (Garble2(FH)) (Garble1) (-1) _);last by wp.
bypr (res{1}) (res{2})=> //.
progress.
apply (eq_trans _ Pr[Garble2(FR).enc(p{1}) @ &m :a = res] _);[
  equiv_deno equivGReal=> // |
  apply eq_sym;equiv_deno equivGarble1=> //;smt].
save.

lemma prHB (A<:GC.PrvIndSec.Adv_t{CV, G, C, R, F}) &m: islossless A.gen_query => islossless A.get_challenge =>
  Pr[Hybrid(A).main(Cst.bound)@ &m:res] = 1%r / 2%r.
proof strict.
intros ll1 ll2.
rewrite -(prFake A &m)=> //.
equiv_deno (_: l{1} = Cst.bound ==> ={res})=> //.
fun*;inline Hybrid(A).main.
wp;call (equivPrvInd A (Garble2(FH)) (Garble2(FF)) (Cst.bound) _);last by wp.
bypr (res{1}) (res{2})=> //.
progress.
equiv_deno equivGFake=> //.
save.

lemma reduction :
  forall (A<:PrvIndSec.Adv_t{CV, G, C, R, F}),
    islossless A.gen_query =>
    islossless A.get_challenge =>
    exists (D<:DKCS.Adv_t),
      forall &m,
        Mrplus.sum (lambda l, let l = l - 1 in Pr[Hybrid(A).main(l) @ &m : res]) (Interval.interval 0 Cst.bound) -
        Mrplus.sum (lambda l, Pr[Hybrid(A).main(l) @ &m : res]) (Interval.interval 0 Cst.bound) =
        2%r * (Cst.bound+1)%r * (Pr[DKCS.Game(DKCS.Dkc, D).main()@ &m:res] - 1%r/2%r)
  by admit. (* TODO: reduction proof *)

lemma reductionSimplified :
  forall (A<:PrvIndSec.Adv_t{CV, G, C, R, F}),
    islossless A.gen_query =>
    islossless A.get_challenge =>
    exists (D<:DKCS.Adv_t),
      forall &m, let l1 = - 1 in let l2 = Cst.bound in
        Pr[Hybrid(A).main(l1) @ &m : res] - Pr[Hybrid(A).main(l2) @ &m : res] =
        2%r * (Cst.bound+1)%r * (Pr[DKCS.Game(DKCS.Dkc, D).main()@ &m:res] - 1%r / 2%r).
proof strict.
progress.
elim (reduction A _ _)=> //.
intros D redt.
exists D.
intros &m.
cut := redt &m=> <-;clear redt.
rewrite (Mrplus.sum_rm _ _ 0) /=;first smt.
rewrite (Mrplus.sum_chind _ (lambda (x:int), x - 1) (lambda (x:int), x + 1)) /=;first smt.
rewrite (Interval.dec_interval 0 Cst.bound _);first smt.
rewrite (Mrplus.sum_rm _ (Interval.interval 0 Cst.bound) ((Cst.bound)%Cst)) /=;first smt.
pose s1 := (Mrplus.sum _ _).
pose s2 := (Mrplus.sum _ _).
cut -> : s1 = s2 by (rewrite /s1 /s2;(congr;last apply Fun.fun_ext);smt).
smt.
save.

lemma _PrvIndDkc :
  forall (A<:PrvIndSec.Adv_t{CV, G, C, R, F}),
    islossless A.gen_query =>
    islossless A.get_challenge =>
    exists (D<:DKCS.Adv_t),
      forall &m,
        `|Pr[PrvIndSec.Game(Garble1, A).main()@ &m:res] - 1%r / 2%r| =
           2%r * (Cst.bound+1)%r * `|Pr[DKCS.Game(DKCS.Dkc, D).main()@ &m:res] - 1%r / 2%r|.
proof strict.
  intros A ? ?.
  elim (reductionSimplified A _ _)=> //.
  intros D red_temp.
  exists D.
  intros &m.
  cut := prH0 A &m=> /= <-.
  rewrite -{1}(prHB A &m)=> //.
  cut := red_temp &m=> /= ->.
  cut -> : forall (a b:real), a >= 0%r => `| a * b | = a * `| b | by smt;smt.
save.
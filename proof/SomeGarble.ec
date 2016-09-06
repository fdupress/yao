(** Definition of a concrete Garble scheme *)

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
require (*--*) Sch.
require (*--*) SchSec. 

require import GarbleTools.
  
require import ArrayExt.

import ForLoop.

(**
  Description of the Garble scheme...
*)
theory SomeGarble.
  require ExtWord.

  (** Words used in the garble scheme *)
  clone import ExtWord as W.

  op bound : int.
  axiom boundInf : 1 < bound.
  
  (** Maximum number of gates that a circuit *)
  op maxGates : int = 2^62 - 1.

  (** DKC security definitions, instantiated with the words defined in W *)
  clone import DKCSec2.DKCSecurity with theory WD <- W.

  (** Tweak theory, instantiated with the words defined in W *)
  clone import Tweak with theory WT <- W.

  (** Auxiliar types used in the definition of the scheme *)
  (** Tokens type **)
  (** 
    Type of the tokens ((X_0^0, X_0^1), ..., (X_n^0, X_n^1)) that represent the randomness used in the garble scheme.

    The tokens are represented as a map, i.e., X_i^b = X.[i,b].
  *)
  type tokens_t = (int * bool, word) fmap.

  (** Gates type *)
  (**
    Type of the gates of both the boolean circuit and the garbled circuit.

    Gates are represented as a map, i.e., the evaluation of gate 'g' with inputs 'a' and 'b' is given by G.[g,a,b].

    This construction can also be seen as a truth table as follows:
      For gate 'g':
        a   b      res
        0   0   G.[g,0,0]
        0   1   G.[g,0,1] 
        1   0   G.[g,1,0] 
        1   1   G.[g,1,1] 

    For example, if gate 'g' represents a boolean XOR gate, the truth table would be as follows:
        a   b      res
        0   0       0
        0   1       1 
        1   0       1 
        1   1       0

    We will consider boolean gates for the circuit and word gates for the garbled circuit.
  *)
  type 'a gates_t = (int * bool * bool, 'a) fmap.

  (** Definition of a circuit *)
  (**
    A circuit is composed by its topology (n, m, q, A, B) and by its functionality (functionality of the gates given by G).

    Again, we will have boolean circuits and word circuits.
  *)
  type 'a funct_t = topo_t * 'a gates_t.

  (** in_dom operation *)
  (**
    Checks if a given key is the domain of a map
  *)
  (*op in_dom (x : 'a) (m : ('a,'b) fmap) = mem (dom m) x.*) 
  
  (** Valid gate predicate *)
  (** 
    A gate is valid if its corresponding truth table is completely defined, i.e., if it has rows that represent all possible entries (0,0/ 0,1 / 1,0/ 1,1).
  *)
  op valid_gates (n q : int) (gg:'a gates_t) =
    range n (n+q) true (fun g b,
                               b /\
                               mem (dom gg) (g, false, false) /\
                               mem (dom gg) (g, false, true) /\
                               mem (dom gg) (g, true, false) /\
                               mem (dom gg) (g, true, true)).

  (** Valid circuit predicate *)
  (**
    A circuit is valid if:
      - n >= 2 (has at least 2 input wires)
      - m >= 1 (has at least 1 output wire) 
      - q >= 1 (has at least 1 gate)
      - m <= q (the number of output wires is compatible with the number of gates)
      - the gates of the circuit are valid
      - forall g : Gates, 0 <= A.[g] < B.[g] < g
  *)
  op valid_circuit (bound : int) (fn : bool funct_t) =
    let (n,m,q,aa,bb) = fst fn in
    let gg = snd fn in
    1 < n /\ 0 < m /\ 0 < q /\ m <= q /\
    n + q - m = bound /\
    size aa = n + q /\ size bb = n + q /\
    valid_gates n q gg /\
    (range n (n + q) true (fun i b,
                               b /\
                               0 <= aa.[i] /\
                               bb.[i] < i /\
                               bb.[i] < n+q-m /\
                               aa.[i] < bb.[i])).

  (**
    Same as above but now in the form of a predicate. 
    
    The main difference is the use of the "forall" quantification instead of a
    ForLoop.range.
  *)
  pred valid_circuitP (bound:int) (f:bool funct_t) =
      let (n, m, q, aa, bb) = fst f in
      1 < n /\ 0 < m /\ 0 < q /\ m <= q /\
      n + q - m = bound /\
      Array.size aa = n + q /\ Array.size bb = n + q /\
      (forall g i1 i2, n <= g < n + q => mem (dom (snd f)) (g, i1, i2)) /\
      (forall i, n <= i < n+q =>
         0 <= aa.[i] /\
         bb.[i] < i /\
         bb.[i] < n+q-m /\
         aa.[i] < bb.[i]).

   (**
     Equivalence between the predicate and the boolean operation.
   *)
   lemma valid_wireinput (bound:int) (f:bool funct_t):
      valid_circuit bound f <=>  valid_circuitP bound f.
    proof. 
      simplify valid_circuitP valid_circuit valid_gates.
      elim (fst f)=> n m q aa bb /=.
      rewrite !rangeb_forall /= /#.
    qed.
      
  (** init_gates operation *)
  (**
    Initialises the gates of a circuit by filling all the entries of the gates' truth tables as follows:
        a   b      res
        0   0    f g 0 0
        0   1    f g 0 1
        1   0    f g 1 0
        1   1    f g 1 1

    'f' takes as input the number of the gate ('g') which gives information about its functionality and computes its value for 'a' and 'b'. For example, if gate g=2 is a XOR gate, the truth table would be generated like:
        a   b          res
        0   0    f 2 0 0 = 0 XOR 0
        0   1    f 2 0 1 = 0 XOR 1
        1   0    f 2 1 0 = 1 XOR 0
        1   1    f 2 1 1 = 1 XOR 1

    Works for both boolean circuits and garbled circuits (word circuits).
  *)
  op init_gates (base size : int) (f:int -> bool -> bool -> 'a) : 'a gates_t =
    let fill = fun g a b gg, gg.[(g, a, b) <- f g a b] in
      range base (base + size) map0
    (fun (g:int) gg, fill g false false (fill g false true (fill g true false (fill g true true gg)))).
    
  (**
    The value of an initalised gate is the application of the function "f" given
    the number of the gate and the input bits.
  *)
  lemma get_initGates (base:int) size (f:int->bool->bool->'a) g a b :
      0 <= size =>
      (init_gates base size f).[(g, a, b)] = if base <= g < base + size then Some (f g a b) else None.
    proof.
      simplify init_gates NewFMap."_.[_]".
      elim/strongInduction size=> j le0_j hrange /=.
      case (0 < j)=> hj; last by smt ["Alt-Ergo"].
      rewrite range_ind_lazy /=; first by simplify => /#. 
      rewrite !getP /=.
      case (g = base + j - 1)=> hg; first simplify => /#. 
      cut neq: forall x y, ((base + j - 1, x, y) = (g, a, b)) = false by simplify => /#.
      cut -> : base + j - 1 = base + (j - 1) by simplify => /#. 
      by simplify => /#. 
    qed.
    
    (**
      If the number of the gate is valid, then it is initalised an it belongs in the
      domain of the init_gates operation.
    *)
    lemma in_dom_init_Gates base size (f:int->bool->bool->'a) (g:int) (a b:bool) :
      0 <= size =>  base <= g < base + size => mem (dom (init_gates base size f)) (g, a, b).
    proof.
      simplify init_gates.    
      elim/strongInduction size=> j le0_j hrange hbase /=.
      case (0 < j)=> hj; last by simplify => /#.
      time rewrite range_ind_lazy /=; first by simplify => /#. 
      rewrite ! dom_set ! in_fsetU.
      case (g = base + j - 1)=> hg; first by case a; case b; smt ["Alt-Ergo"].
      cut -> : base + j - 1 = base + (j - 1) by simplify => /#.
      by simplify => /#. 
    qed.
    
  (** enc operation *)
  (**
    Encodes the result of a line of a truth table.

    The encoding of a line of a truth table is given by E T A' B' (X.[g, G.[g,i,j]]), where
      T = tweak g lsb(A.[g])
      A = X.[A.[g], i]
      B = X.[B.[g], i]
      X = (X_0^0, X_0^1), ..., (X_n^0, X_n^1)
      g = number of the gate
      i = {0,1} - entry of the truth table
      j = {0,1} - entry of the truth table
      G = boolean gates of the circuit
      E = E permutation of the DKC scheme
  *)
  op enc (x:tokens_t) (fn:bool funct_t) (g:int) (x1:bool) (x2:bool) : word =
      let (n, m, q, aa, bb) = fst fn in
      let t1 = (getlsb (oget x.[(aa.[g], false)])) in
      let t2 = (getlsb (oget x.[(bb.[g], false)])) in
      let aa = (oget x.[(aa.[g], x1^^t1)]) in
      let bb = (oget x.[(bb.[g], x2^^t2)]) in
      E (tweak g (getlsb aa) (getlsb bb)) aa bb (oget x.[(g, oget (snd fn).[(g, x1^^t1, x2^^t2)])]).
  
  (** Garble Scheme instantiation as a generalisation of an encryption scheme *)
  (** 
    The garble scheme is instantiated as follows:
      - Input - bool array (wires)
      - Encoding key - tokens (X_0^0, X_0^1), ..., (X_n^0, X_n^1)
      - Garbled input - word array (X_0^s.[0], ..., X_n^s.[n])
      - Input encoding - encode inp.[i] = iK.[i, inp.[i]]
      - Size of garbled input - size of the word array
      - Circuit - bool funct_t (boolean circuit)
      - Garbled circuit - word funct_t (word circuit)
      - Output - bool array (wires)
      - Decoding key - () (there is no decoding key)
      - Garbled output - word array
      - Leakage - topology of the circuit
      - Randomness - tokens (X_0^0, X_0^1), ..., (X_n^0, X_n^1) (encoding key)
      - Valid inputs - the inputs are valid if the circuit is valid and if the size of the input is n
      - Valid randomness - the tokens (X_0^0, X_0^1), ..., (X_n^0, X_n^1) are valid if
        - there is a token 0 (X^0) and a token 1 (X^1) for all positions of the array
        - if the LSBs of every two tokens who are in a pair are different
        - if, in the range [n, n+q[, all 0 tokens have 0 as LSB
      - Circuit leakage function - the circuit leaks its topology
      - Circuit evaluation - (eval fn i).[x] = G.[x, i.[A.[x]], i.[B.[x]]]
      - Garbled circuit evaluation - (evalG FN I).[x] = D (tweak x (lsb(X.[A.[x]])) (lsb(X.[B.[x]])) P.[x, (lsb(X.[A.[x]])), (lsb(X.[B.[x]]))])
      - Circuit garbling - returns the same topology of the circuit to garble together with new gates P, where P.[g,a,b] = E T A B (X.[g, G.[g,a,b]])
      - Generation of the encoding key - the sub array of size n of the tokens array (X_0^0, X_0^1), ..., (X_n^0, X_n^1)
      - Generation of the decoding key - () (no decoding key)
      - Output decoding - LSBs of all the elements of the garbled output
      - pi_sampler - ??????
  *) 
  clone SchSec.SchSecurity as GSch with
    type Sch.Scheme.Input.input_t = bool array,
    type Sch.Scheme.Input.inputK_t = tokens_t,
    type Sch.Scheme.Input.inputG_t = word array,
    
    op Sch.Scheme.Input.encode (iK:inputK_t) (x:input_t) = offun (fun g, oget iK.[(g, x.[g])]) (size x),
    op Sch.Scheme.Input.inputG_len (x: word array) = Array.size x,

    type Sch.Scheme.fun_t = bool funct_t,
    type Sch.Scheme.funG_t = word funct_t,
    type Sch.Scheme.output_t = bool array,
    type Sch.Scheme.outputK_t = unit,
    type Sch.Scheme.outputG_t = word array,
    type Sch.Scheme.leak_t = topo_t,
    type Sch.Scheme.rand_t = tokens_t,

    op Sch.Scheme.validInputs (fn:fun_t) (i:Input.input_t) =
      let (n,m,q,aa,bb) = fst fn in
      let gg = snd fn in
      n + q <= maxGates /\
      valid_circuit bound fn /\ size i = n,

    pred Sch.Scheme.validRand (fn:fun_t) (xx:rand_t) =
      let (n,m,q,aa,bb) = fst fn in
      forall g, 0 <= g < n+q =>
        option_rect false (fun (x:word), true) xx.[(g,false)] /\
        option_rect false (fun (x:word), true) xx.[(g,true)] /\
        !getlsb (oget xx.[(g,false)]) = getlsb (oget xx.[(g,true)]) /\
        (n + q - m <= g => !(getlsb (oget xx.[(g,false)]))),
        
    op Sch.Scheme.phi (fn:fun_t) = fst fn,

    op Sch.Scheme.eval (fn:fun_t) (i:Input.input_t) = 
      let (n, m, q, aa, bb) = fst fn in
      ArrayExt.sub (GarbleTools.evalComplete q i (GarbleTools.extract (fun g x1 x2, (oget (snd fn).[(g, x1, x2)])) aa bb)) (n+q-m) m,
    
    op Sch.Scheme.evalG (fn:funG_t) (i:Input.inputG_t) =
      let (n, m, q, aa, bb) = fst fn in
      let evalGate =
        fun g x1 x2,
          D (tweak g (W.getlsb x1) (W.getlsb x2)) x1 x2 (oget (snd fn).[(g, W.getlsb x1, W.getlsb x2)]) in
      ArrayExt.sub (GarbleTools.evalComplete q i (GarbleTools.extract evalGate aa bb)) (n+q-m) m,

    op Sch.Scheme.funG (fn:fun_t) (r:rand_t) = 
      let (n, m, q, aa, bb) = fst fn in
      (fst fn, init_gates n q (enc r fn)),

    op Sch.Scheme.inputK (fn:fun_t) (r:tokens_t) =
      let (n, m, q, aa, bb) = fst fn in
      filter (fun x y, 0 <= fst x < n) r,

    op Sch.Scheme.outputK (fn:fun_t) (r:rand_t) = tt,

    op Sch.Scheme.decode(k:outputK_t, o: outputG_t) =
      map W.getlsb o,

    op Sch.Scheme.pi_sampler(im : (topo_t * output_t)) =
      let (n,m,q,aa,bb) = fst im in
      let y = snd im in
      let gg = init_gates n q (fun g (a b:bool), if g  < n + q - m then false else y.[g-(n+q-m)]) in
      let x = offun (fun k, false) n in
      ((fst im, gg), x).

  import GSch.Sch.

  (** evali operation *)
  (**
    Evaluation of the circuit given an input in a given index.
  *)
  op evali(fn:fun_t, i:Input.input_t, k:int) =
    let (n, m, q, aa, bb) = fst fn in
    (GarbleTools.evalComplete q i (GarbleTools.extract (fun g x1 x2, (oget (snd fn).[(g, x1, x2)])) aa bb)).[k].
      
  pred validInputsP (plain:fun_t*input_t) =
    let (n, m, q, aa, bb) = fst (fst plain) in
    (n + q)%Int <= maxGates /\ valid_circuitP bound (fst plain) /\ Array.size (snd plain) = n.
  
  (** Correctness proof *)
  (** 
    The garble scheme is correct given that the DKC used to build it
    is also correct.

    Formally, eval(fn,i) = decode (evalG(fn, encode (e,i)))
  *) 
  lemma gsch_correct : D.Correct() => Scheme.Correct().
  proof.
  (*Some simplification before proving the main inductive formula *)
    simplify D.Correct GSch.Sch.Scheme.Correct
      validInputs validRand eval decode outputK
      evalG funG encode inputK => DKCHyp x fn input /=.
    elim fn=> topo ff h_fn /=.
    elim topo h_fn=> n m q aa bb /=.
    simplify fst snd.
    rewrite valid_wireinput.
    simplify valid_circuitP fst snd.
    progress.

    pose n := size input.

    pose inputEnc := GSch.Sch.Scheme.Input.encode (GSch.Sch.Scheme.inputK ((n, m, q, aa, bb), ff) x) input.

    cut ->: W.getlsb = getlsb by done.
    pose eval:= (fun (g : int) (x1 x2 : word),
                   D (tweak g (getlsb x1) (getlsb x2)) x1 x2
                     (oget
                       (init_gates n q (enc x ((n,m,q,aa,bb),ff))).[(g,getlsb x1,getlsb x2)])).

    (* This is the inductive formula that we want to prove *)
    cut main: forall (j:int), 0 <= j < n+q =>
                oget x.[(j, (GarbleTools.evalComplete q input (GarbleTools.extract (fun g x1 x2, oget ff.[(g, x1, x2)]) aa bb)).[j])]
                = (GarbleTools.evalComplete q inputEnc (GarbleTools.extract eval aa bb)).[j];first last.
    (* End case : As soon as we have this formula for all j we apply
        it to the output wire and get the final result with the decode
        and outputK definition *)
      apply arrayP; split; rewrite size_sub /=; first 2 by idtac =>/#.
        by simplify evalComplete; rewrite appendInit_size =>/#.
        rewrite size_map size_sub /=; first 2 by idtac=>/#.
          by (simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#);
          (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#. 
        by trivial.
        by idtac => /#.
        by idtac => /#.
        (simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#) => /#.
      move => j hj.
      rewrite mapE.
        rewrite size_sub; first 2 by idtac => /#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        by (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#.
        exact hj.
      rewrite !get_sub; first 2 by idtac => /#.
        by (simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#) => /#.
        exact hj.
        by idtac => /#.
        by idtac => /#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        by (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#.
        exact hj.
      pose v := (GarbleTools.evalComplete _ _ _).[_].
      cut:= H9 (j + (n + q - m)) _; first by simplify n => /#. 
      progress => /#. 
  
    move => j boundJ.
    cut : j < n + q by idtac=>/#.
    (cut : 0 <= j by idtac=>/#); clear boundJ.
    elim/strongInduction j.
    simplify evalComplete.
    pose ar1 := (GarbleTools.appendInit input q (GarbleTools.extract (fun (g : int) (x1 x2 : bool), oget ff.[(g, x1, x2)]) aa bb)).
    pose ar2 := (GarbleTools.appendInit inputEnc q (GarbleTools.extract eval aa bb)).
    move => k kPos hypRec kbound.
    case (n <= k)=> hk. 
      (* Induction case : use the correction of one gate and the induction hypothesis*)
      rewrite /ar1 /ar2 !appendInit_getFinal; first by idtac=>/#.
        exact H2.
        simplify extract; rewrite get_sub; first 2 by idtac=>/#.
        by (rewrite appendInit_size; first by idtac=>/#) => /#.
        by idtac=>/#.
        by smt.
        (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#.
        exact H2. 
        by smt ["Alt-Ergo"] tmo=120.
      rewrite -/ar1 -/ar2; simplify extract.
      cut -> : (k - 1 + 1 = k) by idtac=>/#.
      rewrite - ! hypRec; first 4 by idtac=>/#.
      simplify eval.
      rewrite get_initGates; first by idtac=>/#. 
      simplify enc fst snd.
      cut ->: (getlsb (oget x.[(aa.[k], ar1.[aa.[k]])]) ^^
               getlsb (oget x.[(aa.[k], false)])) = ar1.[aa.[k]].
        case ar1.[aa.[k]]=> h; last by idtac=>/#.
        cut := H9 aa.[k] _; first clear h; idtac=>/#. 
        move : (getlsb (oget x.[(aa.[k], false)]))=> a.
        move : (getlsb (oget x.[(aa.[k], true)]))=> b.
        move => [_ [_ [HH _ ]]].
        by cut -> : b = ! a by idtac=>/#.
      cut ->: (getlsb (oget x.[(bb.[k], ar1.[bb.[k]])]) ^^
               getlsb (oget x.[(bb.[k], false)])) = ar1.[bb.[k]].
        case ar1.[bb.[k]]=> h; last by idtac=>/#.
        cut := H9 bb.[k] _; first clear h; idtac=>/#.
        move : (getlsb (oget x.[(bb.[k], false)]))=> a.
        move : (getlsb (oget x.[(bb.[k], true)]))=> b.
        move => [_ [_ [HH _ ]]].
        by cut -> : b = ! a by idtac=>/#.
      case (n <= k < n + q); last by idtac=>/#. 
      by rewrite /oget /=; do !rewrite -/(oget _); rewrite DKCHyp.

    (* Base case : prove main for the inputs by using encode and inputK definitions *)
    rewrite /ar1 /ar2 ! appendInit_get1; first 2 by idtac=>/#.
      by simplify inputEnc; rewrite size_offun max_ler => /#.
      by idtac=>/#.
    rewrite -/ar1 -/ar2.
    simplify inputEnc GSch.Sch.Scheme.Input.encode GSch.Sch.Scheme.inputK fst.
    rewrite offunE /=; first by idtac=>/#.
    rewrite filterP /=.
    (cut -> : 0 <= k < n = true by idtac=>/#); simplify.
    by (case (mem (dom x) (k, input.[k])) => hdom; first by done); last by smt.
  qed.
  
  (******************)  
  (** Global values *)
  (******************) 

  (**
    Random values (t and X) for a normal garbling 
  *)
  module R = {
    var t : bool array
    var xx : tokens_t
  }.

  (**
    Circuit to be garbled. To be filled after the sampling of bit c.
  *)
  module C = {
    var f:fun_t
    var x:input_t
    var n:int
    var m:int
    var q:int
    var aa:int array
    var bb:int array
    var gg:bool gates_t
    var v:bool array
  }.

  (**
    Values used in the garble process
  *)
  module G = {
    var pp:word gates_t
    var yy:word array
    var randG: word gates_t
    var a:int
    var b:int
    var g:int
  }.

  (** Initialisers *)
  (**
    Initialises the values of the circuit.
  *)
  module CircuitInit = {
    proc init(p:fun_t*input_t) : unit = {
      var i : int;
      C.f = fst p;
      C.x = snd p;
      (C.n, C.m, C.q, C.aa, C.bb) = fst (fst p);
      C.gg = snd (fst p);
      C.v = offun (fun (i:int), false) (C.n + C.q);
      i = 0;
      while (i < C.n + C.q) {
        C.v.[i] = evali (fst p) C.x i;
        i = i + 1;
      }
    }
  }.

  (**
    Initialises the random values according to a boolean
    that decides if one is to use visible tokens or invisible ones.
  *)
  module RandomInit = {
    proc init(useVisible:bool): unit = {
      var i, tok1, tok2, v, trnd;

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
    } 
  }.

  (**
    "Real" random generator, that inherits EncSecurity.Rand_t.
  *)
  module Rand : GSch.EncSecurity.Rand_t = {
    proc gen(l:topo_t) : tokens_t = {
      var n, m, q, i : int;
      var aa, bb : int array;
      var t : bool;
      
      (n,m,q,aa,bb) = l;
      
      R.t = offun (fun x, false) (n+q);
      R.xx = map0;
      i = 0;
      while (i < n+q) {
        t = $DBool.dbool;
        t = if (i < n+q-m) then t else false;
        R.t.[i] = t;
        R.xx.[(i,false)] = $Dword.dwordLsb t;
        R.xx.[(i,true)] = $Dword.dwordLsb (!t);
        i = i+1;
      }

      return R.xx;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)

  lemma CircuitInit_lossless: islossless CircuitInit.init. 
  proof. by proc; while true (C.n + C.q - i); auto => /#. qed.

  lemma RandomInit_lossless: islossless RandomInit.init.
  proof.
    proc => //.
    while true (C.n + C.q - i).
      auto; progress; [smt| | |smt];
      expect 2 by cut:= Dword.dwordLsb_lossless; rewrite /weight /True=> ->.
    by auto => /#.
  qed.

  lemma R_lossless (l' : topo_t): phoare [Rand.gen : l = l' /\ let (n,m,q,aa,bb) = l' in 1 < n /\ 0 < m /\ 0 < q /\ m <= q ==> true] = 1%r.
  proof.
    proc => //.
    while (0 <= i <= n+q) (n+q-i).
      by move => z; auto; progress; expect 6 by smt.
    by auto => /#.
  qed.
  
  (*******************************************************)
  (* Lemmas concerning the initialisation of the circuit *)
  (*******************************************************)

  pred validBound (bound:int) (plain:fun_t*input_t) =
    let (n,m,q,aa,bb) = fst (fst plain) in
    bound = n + q.
  
  lemma CircuitInitH (plain:fun_t*input_t):
    validInputsP plain =>
    validBound DKCSecurity.bound plain =>
    hoare[CircuitInit.init: p = plain ==>
                   C.f = fst plain /\
                   C.x = snd plain /\
                   (C.n, C.m, C.q, C.aa, C.bb) = fst (fst plain) /\
                   C.gg = snd (fst plain) /\
                   size C.v = (C.n + C.q) /\
                   validInputsP (C.f, C.x) /\
                   DKCSecurity.bound = C.n + C.q].
  proof.
    move=> vIn vIn'; proc => //.
    while (size C.v = C.n + C.q).
      by auto; progress; rewrite size_set. 
    auto=> //= &m p_plain; subst.
    move: vIn vIn'; rewrite /validInputsP /validBound /valid_circuitP /fst /fst /fst /snd /snd.
    elim plain=> [fn] ii /=. 
    elim (fn.`1); progress. 
    by rewrite size_offun; rewrite max_ler => /#. 
  qed.

  (**
    Equivalence between the initialisations when the selected
    query is the same  
  *)  
  equiv CircuitInitEquiv: CircuitInit.init ~ CircuitInit.init:
      ={p} /\
      (validInputsP p){1} /\
      validBound DKCSecurity.bound p{1} ==>
      ={glob C} /\
      size C.v{1} = (C.n + C.q){1} /\
      C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
      validInputsP (C.f, C.x){1} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\
      (forall i, 0 <= i < C.n{2} => C.v{2}.[i] = C.x{2}.[i]) /\
      (forall i, C.n <= i < C.n + C.q => C.v{2}.[i] = oget C.gg.[(i, C.v{2}.[C.aa{2}.[i]], C.v{2}.[C.bb.[i]])]){2}.
  proof. 
    proc => //.
    while ((Array.size C.v = C.n + C.q){1} /\
      ={glob C, i, p} /\
      fst p{2} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){2} /\
      0 <= C.n{2} /\
      (forall j, C.n <= j < C.n + C.q => 0 <= C.aa.[j] < j){2} /\
      (forall j, C.n <= j < C.n + C.q => 0 <= C.bb.[j] < j){2} /\
      (forall j, C.n <= j < i => C.v{2}.[j] = oget C.gg.[(j, C.v{2}.[C.aa{2}.[j]], C.v{2}.[C.bb.[j]])]){2} /\
      (forall j,   0 <= j < i => C.v{2}.[j] = evali (fst p) C.x j){2} /\
      0 < C.q{2} /\
      size C.x{2} = C.n{2}).
        auto=> //=.
        move=> &1 &2 [[lenCv]] [[[eqCv [eqCb [eqCq [eqCn [eqCf [eqCx [eqCm [eqCa eqCg]]]]]]]]]] [eqi eqp]; subst.
        rewrite /fst; elim (p{2})=> fn ii /=.
        elim (fn)=> tt gg.
        elim (tt)=> n m q aa bb [[[]]]; subst.  
        move=> n_Cn m_Cm q_Cq aa_Caa bb_Cbb gg_Cgg; subst.
        move=> [leq0_Cn] [vA] [vB] [vGates] [vWires] [lt0_q] lenCx [i_lt_CnCq] H {H}.
        split=> //=; first by rewrite size_set =>/#.
        split; first by idtac => /#. 
        split=> //.
        split=> //.
        split.
          move=> j j_bnd; case (i{2} = j).
            move=> i_j; subst; rewrite !get_set //=; first 3 by idtac=>/#.
            cut -> /=: (C.aa{2}.[j] = j) = false by idtac=>/#.
            cut -> /=: (C.bb{2}.[j] = j) = false by idtac=>/#.
            rewrite /evali /fst /snd /=.
            rewrite /evalComplete appendInit_getFinal //; first by idtac=>/#. 
              by rewrite /extract //= !get_sub //=; smt.
            rewrite /extract (_: j - 1 + 1 = j) //=; first by idtac=>/#. 
              congr; congr; split=> //.
                by rewrite vWires; first by idtac=>/#.
                by rewrite vWires; first by idtac=>/#.
            rewrite -neqF=> j_neq_i; cut j_lt_i: j < i{2} by idtac=>/#.
            rewrite get_set /=; first by idtac=>/#.
            rewrite vGates; first by idtac=>/#.
            cut ->: forall x, C.v{2}.[i{2} <- x].[C.aa{2}.[j]] = C.v{2}.[C.aa{2}.[j]] by smt. 
            cut ->: forall x, C.v{2}.[i{2} <- x].[C.bb{2}.[j]] = C.v{2}.[C.bb{2}.[j]] by smt.
            by cut ->: j = i{2} <=> false by idtac=>/#. 
        split=> //=.
          move=> j j_bnd; case (i{2} = j).
            by move=> i_j; subst; rewrite !get_set //=; first by idtac=>/#.
            rewrite -neqF=> j_neq_i; cut j_lt_i: j < i{2} by idtac=>/#.
            rewrite get_set /=; first by idtac=>/#.
            rewrite vWires; first by idtac=>/#.
            by cut ->: j = i{2} <=> false by idtac=>/#. 
    auto; move=> &1 &2 [eqP [vIn] vIn'] //=; subst.
    move: vIn vIn'; rewrite /validInputsP /validBound /validCircuitP /fst /fst /fst /snd /snd //=.
    elim (p{2})=> fn ii /=; subst.
    elim (fn)=> tt gg. 
    elim (tt) => n m q aa bb /=; subst.
    progress.
      by rewrite size_offun max_ler; first by idtac=>/#. 
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by (rewrite H9; first by idtac=>/#); simplify evali fst evalComplete; (rewrite appendInit_get1; first by idtac=>/#) => /#.  
      by idtac=>/#.
  qed.

  (**
    Equivalence between the initialisations when the selected
    query is not the same  
  *)  
  equiv InitEquiv_rnd: CircuitInit.init ~ CircuitInit.init:
    GSch.EncSecurity.queryValid_IND (p{1}, p{2}) ==>
    ={C.n, C.m, C.q, C.aa, C.bb} /\
    (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i]) /\
    (eval C.f C.x){1} = (eval C.f C.x){2} /\
    (((C.n, C.m, C.q, C.aa, C.bb), C.gg) = C.f /\
    Array.size C.v = (C.n + C.q) /\
    validInputsP (C.f, C.x)){1} /\
    (forall i, 0 <= i < C.n{1} => C.v{1}.[i] = C.x{1}.[i]) /\
    (((C.n, C.m, C.q, C.aa, C.bb), C.gg) = C.f /\
    Array.size C.v = (C.n + C.q) /\
    validInputsP (C.f, C.x)){2} /\
    (forall i, 0 <= i < C.n{1} => C.v{2}.[i] = C.x{2}.[i]).
  proof.
    proc => //.
    seq 6 6: (={C.v,C.n,C.m,C.q,C.aa,C.bb,i} /\
      i{1} = 0 /\
      Array.size C.v{1} = C.n{1} + C.q{1} /\
      eval C.f{1} C.x{1} = eval C.f{2} C.x{2} /\
      ((C.n,C.m,C.q,C.aa,C.bb),C.gg){1} = C.f{1} /\
      ((C.n,C.m,C.q,C.aa,C.bb),C.gg){2} = C.f{2} /\
      C.f{1} = p{1}.`1 /\
      C.f{2} = p{2}.`1 /\
      size C.x{1} = C.n{1} /\
      size C.x{2} = C.n{2} /\
      size C.x{1} + C.q{1} <= maxGates /\
      1 < size C.x{1} /\
      0 < C.m{1} /\
      0 < C.q{1} /\
      C.m{1} <= C.q{1} /\
      C.n{1} + C.q{1} - C.m{1} = bound /\
      size C.aa{1} = C.n{1} + C.q{1} /\
      size C.bb{1} = C.n{1} + C.q{1} /\
      (forall g b1 b2,
        C.n{1} <= g < C.n{1} + C.q{1} => mem (dom C.gg{1}) (g,b1,b2)) /\
      (forall g b1 b2,
        C.n{1} <= g < C.n{1} + C.q{1} => mem (dom C.gg{2}) (g,b1,b2)) /\
      (forall i,
        C.n{1} <= i < C.n{1} + C.q{1} =>
        0 <= C.aa{1}.[i] /\ C.bb{1}.[i] < i /\
        C.bb{1}.[i] < C.n{1} + C.q{1} - C.m{1} /\ C.aa{1}.[i] < C.bb{1}.[i])).
        auto; rewrite /queryValid_IND /valid_plain /leak.
        rewrite /validInputs /validInputs /valid_circuit /validGG /phi /phi /fst /fst /fst /snd /snd /snd //=.
        move=> &1 &2.
        elim (p{1})=> fn1 ii1 /=.
        elim (fn1)=> tt1 gg1.
        elim (tt1)=> n1 m1 q1 aa1 bb1 /=; subst.
        elim (p{2})=> fn2 ii2 /=.
        elim (fn2)=> tt2 gg2 /=; subst.
        elim (tt2)=> n2 m2 q2 aa2 bb2 /=; subst.
        cut ->: (fun i b, b /\ 0 <= aa1.[i] /\ bb1.[i] < i /\ bb1.[i] < n1 + q1 - m1 /\ aa1.[i] < bb1.[i])
                = (fun i b,
                    b /\ (fun j, 0 <= aa1.[j] /\ bb1.[j] < j /\ bb1.[j] < n1 + q1 - m1 /\ aa1.[j] < bb1.[j]) i)
          by done.
        cut ->: (fun i b, b /\ 0 <= aa2.[i] /\ bb2.[i] < i /\ bb2.[i] < n2 + q2 - m2 /\ aa2.[i] < bb2.[i])
                = (fun i b,
                    b /\ (fun j, 0 <= aa2.[j] /\ bb2.[j] < j /\ bb2.[j] < n2 + q2 - m2 /\ aa2.[j] < bb2.[j]) i)
          by done.
        rewrite !rangeb_forall //=.
        progress [-split].
        do 11!(split; first by smt).
        split; first by move=> g b1 b2 g_bnd; cut:= H7 g _=> //; case b1; case b2 => /#.
        split; first by move=> g b1 b2 g_bnd; cut:= H17 g _; [idtac=>/#|]; case b1; case b2.
        by idtac=>/#.
    conseq (_: _ ==>
      (forall j,
        C.n{2} + C.q{2} - C.m{2} <= j < C.n{2} + C.q{2} =>
        C.v{1}.[j] = C.v{2}.[j]) /\
        size C.v{1} = C.n{2} + C.q{2} /\
        size C.v{2} = C.n{2} + C.q{2} /\
        (forall j, 0 <= j < C.n{2} => C.v{1}.[j] = C.x{1}.[j]) /\
        (forall j, 0 <= j < C.n{2} => C.v{2}.[j] = C.x{2}.[j])).
          by progress; expect 3 by idtac=>/#.
    while (={C.n,C.m,C.q,C.aa,C.bb,i} /\
          0 <= C.q{2} /\
          0 <= C.n{2} + C.q{2} - C.m{2} /\
          (Array.size C.v = C.n + C.q){1} /\
          (Array.size C.v = C.n + C.q){2} /\
          (eval C.f C.x){1} = (eval C.f C.x){2} /\
          (forall j, C.n{1} + C.q{1} - C.m{1} <= j < i{1} => C.v{1}.[j] = C.v{2}.[j]) /\
          (forall j, 0 <= j < i{1} /\ j < C.n{1}=> C.v{2}.[j] = C.x{2}.[j]) /\
          C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
          (forall j, 0 <= j < i{1} /\ j < C.n{1} => C.v{1}.[j] = C.x{1}.[j]) /\
          C.f{2} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){2} /\
          p{1}.`1 = C.f{1} /\
          p{2}.`1 = C.f{2} /\
          (C.n = size C.x){1} /\ (C.n = size C.x){2}).
      auto.
      progress; first 2 by rewrite size_set.
        rewrite !Array.get_set; first 2 by idtac=>/#.
        move: H3; rewrite /eval /eval /evali /fst /fst /snd H7 H8 /=.
        pose w := size C.x{1} + C.q{2} - C.m{2}.
        move=> H3.
        cut: (sub (evalComplete C.q{2} C.x{1}
                      (extract (fun g x1 x2,
                                  oget C.gg{1}.[(g, x1, x2)]) C.aa{2} C.bb{2}))
                    w C.m{2}).[i{2}-w] =
               (sub (evalComplete C.q{2} C.x{2}
                      (extract (fun g x1 x2,
                                  oget C.gg{2}.[(g, x1, x2)]) C.aa{2} C.bb{2}))
                    w C.m{2}).[i{2}-w]
            by rewrite H3.
            case ((i = j){2}) => hj; rewrite get_sub; smt ["Alt-Ergo"] tmo=5. 
          rewrite Array.get_set; first by idtac=>/#.
          case ((i = j){2}) => hj;
            rewrite /evali /evalComplete ?appendInit_get1; smt.
          rewrite Array.get_set; first by idtac=>/#.
          by case ((i = j){2}) => _;
            rewrite /evali /evalComplete ?appendInit_get1; smt.
    by skip; progress => /#. 
  qed.

  (**********************************************************)
  (* Lemmas concerning the initialisation of the randomness *)
  (**********************************************************)

  lemma get_set_neq (m:('a,'b) fmap) x x' y: x <> x' => m.[x <- y].[x'] = m.[x'].
  proof. by rewrite -neqF getP => hxx' => /#. qed.

  lemma RandomInitH:
    hoare[RandomInit.init: 0 <= C.m <= C.n + C.q /\
                     fst C.f = (C.n, C.m, C.q, C.aa, C.bb) ==>
                     validRand C.f R.xx /\
                     Array.size R.t = (C.n+C.q)].
  proof.
    proc => //.
    while (0 <= C.m <= C.n + C.q /\
      Array.size R.t = C.n + C.q /\
      (forall (j:int), 0 <= j => j < i =>
        option_rect false (fun (x : word), true) R.xx.[(j, false)] /\
        option_rect false (fun (x : word), true) R.xx.[(j, true)] /\
        getlsb (oget R.xx.[(j, false)]) <> getlsb (oget R.xx.[(j, true)]) /\
        (C.n + C.q - C.m <= j => !(getlsb (oget R.xx.[(j, false)]))))); first last.
          auto; progress [-split].
          split; first by smt.
          progress [-split].
          rewrite /validRand /validRand; elim (fst C.f{hr}) H1=> n m q aa bb [-> -> -> -> ->] /=.
          by split=> //= i [i_lb i_ub]; move: (H6 i _ _); first 2 by idtac=>/#.
    auto; progress.
      by rewrite size_set.
      case (j < i{hr})=> h.
        by rewrite !get_set_neq; expect 3 by idtac=>/#.
        cut ->: i{hr} = j by idtac=>/#.
        rewrite !getP /=.
        by case (useVisible{hr} && C.v{hr}.[j]).
      case (j < i{hr})=> h.
        by rewrite !get_set_neq; expect 3 by idtac=>/#.
        cut ->: i{hr} = j by idtac=>/#.
        rewrite !getP /=.
        by case (useVisible{hr} && C.v{hr}.[j])=> //=.
      case (j < i{hr})=> h.
        by rewrite !get_set_neq; expect 5 by idtac=>/#.
        cut ->: i{hr} = j by idtac=>/#.
        rewrite !getP /=.
        by case (useVisible{hr} && C.v{hr}.[j]); rewrite //= oget_some //=; smt. 
      case (j < i{hr})=> h.
        by rewrite !get_set_neq; expect 3 by idtac=>/#.
        cut ->: i{hr} = j by idtac=>/#.
        rewrite !getP /=.
        by case (useVisible{hr} && C.v{hr}.[j]); rewrite //= oget_some //=; smt.
    qed.

  (**
    Random equivalence when visible wires are being used in both sides
  *)
  equiv RandomInitEquiv: RandomInit.init ~ RandomInit.init:
    ={useVisible, C.n, C.m, C.q, C.aa, C.bb} /\
    (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
      C.v{1}.[i] = C.v{2}.[i]) /\
      (0 <= C.m <= C.n + C.q){1} /\
      useVisible{1} /\
      (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
      ={R.t} /\
      (forall g, 0 <= g < (C.n + C.q){1} => R.xx.[(g, C.v.[g])]{1} = R.xx.[(g, C.v.[g])]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => R.xx.[(g, !C.v.[g])]{1} = R.xx.[(g, !C.v.[g])]{2}) /\
      (0 <= C.m <= C.n + C.q /\
      validRand C.f R.xx /\
      Array.size R.t = (C.n+C.q)){1}.
  proof.
    conseq (_: _ ==>
      ={R.t} /\
      (forall g, 0 <= g < C.n{1} + C.q{1} => R.xx.[(g,C.v.[g])]{1} = R.xx.[(g,C.v.[g])]{2}) /\
      (forall g, 0 <= g < C.n{1} + C.q{1} => R.xx.[(g,!C.v.[g])]{1} = R.xx.[(g,!C.v.[g])]{2}))
      RandomInitH=> //=.
    proc => //.
    while (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i, R.t} /\
      (forall g, 0 <= g < i{1} =>
        R.xx.[(g, C.v.[g])]{1} = R.xx.[(g, C.v.[g])]{2}) /\
      (forall g, 0 <= g < i{1} =>
        R.xx.[(g, !C.v.[g])]{1} = R.xx.[(g, !C.v.[g])]{2}) /\
      (0 <= C.m <= C.n + C.q){1} /\
      (Array.size R.t = C.n + C.q){1} /\
        useVisible{1} /\
      (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i]));
        first last.
        auto; progress;
          first 2 by rewrite !map0P.
          by rewrite size_offun max_ler => /#. 
          by rewrite H6 => /#. 
          by rewrite H7 => /#. 
    (auto; progress; rewrite H4 //=; first by smt); first 4 by idtac=>/#. 
      by rewrite !getP => /#. 
      by rewrite !getP => /#. 
      by rewrite size_set.
  qed.
    
  pred t_xor (sup:int) (t1 t2 v:bool array) = forall i,
      0 <= i < sup =>
      t1.[i] = t2.[i] ^^ v.[i].

  (**
    Random equivalence when visible wires are being used in just one side
  *)
  equiv RandomGenClassicVisibleE:
    RandomInit.init ~ RandomInit.init:
      ={glob C} /\ fst C.f{2} = (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) /\
      0 <= C.n{2} + C.q{2} /\
      useVisible{1} = true /\
      useVisible{2} = false ==>
      ={R.xx} /\
      (validRand C.f{1} R.xx{1}) /\
      (forall i v, 0 <= i < C.n + C.q => getlsb (oget R.xx.[(i, v)]) = v^^R.t.[i]){2} /\
      Array.size R.t{1} = (C.n{1}+C.q{1}) /\
      t_xor (C.n{1} + C.q{1}) R.t{1} R.t{2} C.v{1}.
  proof.
    proc => //; while (={i, R.xx, glob C} /\
                useVisible{1} = true /\
                useVisible{2} = false /\
                t_xor i{1} R.t{1} R.t{2} C.v{1} /\
                0 <= i{2} /\
                size R.t{1} = C.n{2} + C.q{2} /\
                size R.t{2} = C.n{2} + C.q{2} /\
                (forall j v, 0 <= j < i => getlsb (oget R.xx.[(j, v)]) = v^^R.t.[j]){2} /\ 
                (forall (j:int), 0 <= j < i =>
                  option_rect false (fun (x : word), true) R.xx.[(j, false)] /\
                  option_rect false (fun (x : word), true) R.xx.[(j, true)] /\
                  getlsb (oget R.xx.[(j, false)]) <> getlsb (oget R.xx.[(j, true)]) /\
                  (C.n + C.q - C.m <= j => !(getlsb (oget R.xx.[(j, false)])))){2} /\
                (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){2}).
      case (C.v{1}.[i{1}] = false).
        do !(wp; rnd); skip; progress=> //; first 5 by idtac=>/#. 
          by rewrite /t_xor //=; progress => //; smt. 
          by idtac=>/#.
          by rewrite size_set.    
          by rewrite size_set.
        rewrite !getP.
        case (i{2} = j)=> h;[cut := H16;cut := H12;case v0=> hv0 /= |cut := H3 j v0 _].
          by rewrite h //=; progress; rewrite xorC xor_true; (rewrite get_set; first by idtac=>/#); simplify; rewrite (Dword.lsb_dwordLsb (! (j < C.n{2} + C.q{2} - C.m{2} && trndL))) //=. 
          by rewrite h //=; progress; rewrite xorC xor_false; (rewrite ?get_set; first by idtac=>/#); simplify; rewrite (Dword.lsb_dwordLsb (j < C.n{2} + C.q{2} - C.m{2} && trndL)) //= /#. 
          by idtac=>/#.
          by rewrite get_set => /#. 
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        by rewrite !getP; case (i{2} = j)=> h;[ |cut := H4 j _]; smt.
        by rewrite !getP; case (i{2} = j)=> h;[ |cut := H4 j _]; smt.
      swap{1} 4 1; do 2!(wp; rnd); wp; rnd (fun (x:bool), !x); skip;(progress=> //;first 6 smt).
        by rewrite set_set => /#. 
        by simplify t_xor; progress; cut:= H i0; smt.
        by idtac=>/#. 
        by rewrite size_set. 
        by rewrite size_set.  
        rewrite !getP. 
        case (i{2} = j)=> h.
          subst; case v0=> h /=.
            by (rewrite get_set; first by idtac=>/#); rewrite xorC xor_true //=; smt.
            by (rewrite get_set; first by idtac=>/#); rewrite xorC xor_false //=; smt.
          by cut:= H3 j v0; smt.
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        by rewrite !getP; case (i{2} = j)=> h;[subst=> /= |cut := H4 j]; smt.
        by rewrite !getP; case (i{2} = j)=> h;[ |cut := H4 j]; smt.
    (wp; skip; progress=> //; simplify validRand validRand; first by idtac=>/#); last 8 by idtac=>/#. 
      by rewrite size_offun max_ler => /#.
      by rewrite size_offun max_ler => /#.
  qed.

  lemma sch_is_pi: GSch.EncSecurity.pi_sampler_works ().
  proof.
    rewrite /GSch.EncSecurity.pi_sampler_works=> plain.
    simplify validCircuit validInputs GSch.EncSecurity.Encryption.valid_plain GSch.EncSecurity.Encryption.leak GSch.EncSecurity.Encryption.pi_sampler pi_sampler phi eval.
    elim plain=> p1 p2 hplain.
    elim p1 hplain => topo1 x1 hp1.
    elim topo1 hp1 => n m q aa bb hplain.
    simplify fst snd.
    progress.
     rewrite {1} /GarbleTools.evalComplete /=.
     pose ev := GarbleTools.evalComplete _ _ _.
     apply arrayP; split.
       rewrite size_sub; first 2 by idtac => /#.
       rewrite appendInit_size; first by idtac=>/#.
       rewrite size_offun max_ler => /#. 
     rewrite size_sub; first 2 by idtac=>/#.
       by simplify ev evalComplete;
         rewrite appendInit_size => /#. 
       done.
    rewrite size_sub; first 2 by idtac => /#.
      by (rewrite appendInit_size; first by idtac => /#); rewrite size_offun max_ler => /#.
    move=> i hi; rewrite !get_sub; first 2 by idtac=>/#.
       rewrite appendInit_size; first by idtac => /#.
       by rewrite size_offun max_ler => /#.
       by done.
       by idtac=>/#.
       by idtac=>/#.
       by (simplify ev evalComplete; rewrite appendInit_size => /#) => /#. 
       by done.
     rewrite appendInit_get2.
       by rewrite ?size_offun ?max_ler; first 2 by idtac=>/#.
       by idtac=>/#.
     rewrite {1} /GarbleTools.extract /=.
     rewrite get_initGates; first by idtac=>/#.
     cut ->: (n <= i + (n + q - m) - 1 + 1 < n + q) = true by idtac=>/#.
     simplify.
     rewrite oget_some.
     rewrite get_sub; first 2 by idtac=>/#.
       by (simplify ev evalComplete; rewrite appendInit_size => /#) => /#. 
       by idtac=>/#.       
       by idtac=>/#.
     by idtac=>/#.
     by idtac=>/#.
     by idtac=>/#.
     by idtac=>/#.  
     by idtac=>/#.
     by idtac=>/#.
     by idtac=>/#.
     by idtac=>/#.
     simplify valid_gates.
     pose {1} k := q.
     cut: k <= q by idtac=>/#.
     cut: 0 <= k by idtac=>/#.
     elim/intind k; first by smt. 
       progress. 
       rewrite range_ind_lazy /=; first by idtac=>/#.
       cut -> : n + (i + 1) - 1 = n + i by idtac=>/#.
       rewrite H0 /=; first by idtac=>/#.
       cut ltiq: i < q by smt.
       split; first by simplify snd; apply in_dom_init_Gates; expect 2 idtac=>/#.
       split; first by simplify snd; apply in_dom_init_Gates; expect 2 idtac=>/#.
       by split; simplify snd; apply in_dom_init_Gates; expect 4 idtac=>/#.
     by move : hplain; simplify valid_circuit fst snd => /#.
     by rewrite size_offun max_ler => /#. 
  qed.
end SomeGarble.
export SomeGarble.
 
  (*lemma sch_is_ind (A <: GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,R',C,DKC_Adv,DKCp}) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>    
      `|2%r * Pr[GSch.EncSecurity.Game_IND(Rand,A).main()@ &m:res] - 1%r| =
        2%r * (bound)%r * `|2%r * Pr[DKCSecurity.Game(DKC, DKC_Adv(DKCSecurity.DKC, A)).main()@ &m:res] - 1%r|.
    proof. admit. qed.

  lemma gsch_is_sim (A <: GSch.EncSecurity.Adv_SIM_t {R}) (Adv <: Adv_DKC_t) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
    `|2%r * Pr[GSch.EncSecurity.Game_SIM(Rand,GSch.EncSecurity.SIM(Rand),A).main()@ &m:res] - 1%r| <=
    2%r * (bound)%r * `|2%r * Pr[GameDKC(Adv).main()@ &m:res] - 1%r|.
  proof. admit. qed.*)
      
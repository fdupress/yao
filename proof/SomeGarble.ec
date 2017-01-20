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

  op nwires : int.
  axiom nwires_pos : 2 < nwires.
  
  (** Maximum number of gates that a circuit *)
  op maxGates : int = 2^62 - 1.

  (** DKC security definitions, instantiated with the words defined in W *)
  clone import DKCSec2.DKCSecurity with
    theory WD <- W,
    op bound = nwires,
    op boundl = SomeGarble.bound.

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
    valid_gates n q gg /\ n + q = nwires /\
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
         aa.[i] < bb.[i]) /\ n + q = nwires.

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
      case (0 < j)=> hj; last by smt full tmo=30. 
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

  clone Sch.Scheme as Inp with
    type Input.input_t = bool array,
    type Input.inputK_t = tokens_t,
    type Input.inputG_t = word array,
    
    op Input.encode (iK:inputK_t) (x:input_t) = offun (fun g, oget iK.[(g, x.[g])]) (size x),
    op Input.inputG_len (x: word array) = Array.size x.  
  
  clone Inp as GSch with
    type fun_t = bool funct_t,
    type funG_t = word funct_t,
    type output_t = bool array,
    type outputK_t = unit,
    type outputG_t = word array,
    type leak_t = topo_t,
    type rand_t = tokens_t,

    op validInputs (fn:fun_t) (i:Input.input_t) =
      let (n,m,q,aa,bb) = fst fn in
      let gg = snd fn in
      n + q <= maxGates /\
      valid_circuit bound fn /\ size i = n,

    pred validRand (fn:fun_t) (xx:rand_t) =
      let (n,m,q,aa,bb) = fst fn in
      forall g, 0 <= g < n+q =>
        option_rect false (fun (x:word), true) xx.[(g,false)] /\
        option_rect false (fun (x:word), true) xx.[(g,true)] /\
        !getlsb (oget xx.[(g,false)]) = getlsb (oget xx.[(g,true)]) /\
        (n + q - m <= g => !(getlsb (oget xx.[(g,false)]))),
        
    op phi (fn:fun_t) = fst fn,

    op eval (fn:fun_t) (i:Input.input_t) = 
      let (n, m, q, aa, bb) = fst fn in
      ArrayExt.sub (GarbleTools.evalComplete q i (GarbleTools.extract (fun g x1 x2, (oget (snd fn).[(g, x1, x2)])) aa bb)) (n+q-m) m,
    
    op evalG (fn:funG_t) (i:Input.inputG_t) =
      let (n, m, q, aa, bb) = fst fn in
      let evalGate =
        fun g x1 x2,
          D (tweak g (W.getlsb x1) (W.getlsb x2)) x1 x2 (oget (snd fn).[(g, W.getlsb x1, W.getlsb x2)]) in
      ArrayExt.sub (GarbleTools.evalComplete q i (GarbleTools.extract evalGate aa bb)) (n+q-m) m,

    op funG (fn:fun_t) (r:rand_t) = 
      let (n, m, q, aa, bb) = fst fn in
      (fst fn, init_gates n q (enc r fn)),

    op inputK (fn:fun_t) (r:tokens_t) =
      let (n, m, q, aa, bb) = fst fn in
      filter (fun x y, 0 <= fst x < n) r,

    op outputK (fn:fun_t) (r:rand_t) = tt,

    op decode(k:outputK_t, o: outputG_t) =
      map W.getlsb o,

    op pi_sampler(im : (topo_t * output_t)) =
      let (n,m,q,aa,bb) = fst im in
      let y = snd im in
      let gg = init_gates n q (fun g (a b:bool), if g  < n + q - m then false else y.[g-(n+q-m)]) in
      let x = offun (fun k, false) n in
      ((fst im, gg), x).

  clone import SchSec.SchSecurity as Sec with
    theory Sch.Scheme <- GSch.
 
  import Sec.
  import GSch.
  
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
  
  lemma gsch_correct : D.Correct() => GSch.Correct().
  proof.
  (*Some simplification before proving the main inductive formula *)
    simplify D.Correct GSch.Correct
      validInputs validRand eval decode outputK
      evalG funG encode inputK => DKCHyp x fn input /=.
    elim fn=> topo ff h_fn /=.
    elim topo h_fn=> n m q aa bb /=.
    simplify fst snd.
    rewrite valid_wireinput.
    simplify valid_circuitP fst snd.
    progress.

    pose n := size input.

    pose inputEnc := GSch.Input.encode (GSch.inputK ((n, m, q, aa, bb), ff) x) input.

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
      cut:= H10 (j + (n + q - m)) _; first by simplify n => /#. 
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
        simplify extract; congr; expect 2 by
          ((rewrite get_sub; first 2 by trivial); last 2 by idtac=>/#); 
          (rewrite appendInit_size; first by idtac=>/#);
          (simplify inputEnc encode; rewrite size_offun max_ler => /#). 
      rewrite -/ar1 -/ar2; simplify extract.
      cut -> : (k - 1 + 1 = k) by idtac=>/#.
      rewrite - ! hypRec; first 4 by idtac=>/#.
      simplify eval.
      rewrite get_initGates; first by idtac=>/#. 
      simplify enc fst snd.
      cut ->: (getlsb (oget x.[(aa.[k], ar1.[aa.[k]])]) ^^
               getlsb (oget x.[(aa.[k], false)])) = ar1.[aa.[k]].
        case ar1.[aa.[k]]=> h; last by idtac=>/#.
        cut := H10 aa.[k] _; first clear h; idtac=>/#. 
        move : (getlsb (oget x.[(aa.[k], false)]))=> a.
        move : (getlsb (oget x.[(aa.[k], true)]))=> b.
        move => [_ [_ [HH _ ]]].
        by cut -> : b = ! a by idtac=>/#.
      cut ->: (getlsb (oget x.[(bb.[k], ar1.[bb.[k]])]) ^^
               getlsb (oget x.[(bb.[k], false)])) = ar1.[bb.[k]].
        case ar1.[bb.[k]]=> h; last by idtac=>/#.
        cut := H10 bb.[k] _; first clear h; idtac=>/#.
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
    simplify inputEnc GSch.Input.encode GSch.inputK fst.
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
  module Rand : EncSecurity.Rand_t = {
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
      move => z; auto; progress; expect 6 by smt ["Alt-Ergo"].
    by auto => /#.
  qed.
  
  (*******************************************************)
  (* Lemmas concerning the initialisation of the circuit *)
  (*******************************************************)

  pred validBound (bound:int) (plain:fun_t*input_t) =
    let (n,m,q,aa,bb) = fst (fst plain) in
    DKCSecurity.bound = n + q.
  
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

  lemma CircuitInitH' (plain:fun_t*input_t):
    validInputsP plain =>
    hoare[CircuitInit.init: p = plain ==>
                   C.f = fst plain /\
                   C.x = snd plain /\
                   (C.n, C.m, C.q, C.aa, C.bb) = fst (fst plain) /\
                   C.gg = snd (fst plain) /\
                   size C.v = (C.n + C.q) /\
                   validInputsP (C.f, C.x)].
  proof.
    move=> vIn; proc => //.
    while (size C.v = C.n + C.q).
      by auto; progress; rewrite size_set. 
    auto=> //= &m p_plain; subst.
    move: vIn; rewrite /validInputsP /validBound /valid_circuitP /fst /fst /fst /snd /snd.
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

  equiv CircuitInitEquiv': CircuitInit.init ~ CircuitInit.init:
      ={p} /\
      (validInputsP p){1} ==>
      ={glob C} /\
      size C.v{1} = (C.n + C.q){1} /\
      C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
      validInputsP (C.f, C.x){1} /\
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
    auto; move=> &1 &2 [eqP vIn] //=; subst.
    move: vIn; rewrite /validInputsP /validCircuitP /fst /fst /fst /snd /snd //=.
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
      by (rewrite H8; first by idtac=>/#); simplify evali fst evalComplete; (rewrite appendInit_get1; first by idtac=>/#) => /#.  
      by idtac=>/#.
  qed.
  
  (**
    Equivalence between the initialisations when the selected
    query is not the same  
  *)  
  equiv InitEquiv_rnd: CircuitInit.init ~ CircuitInit.init:
    EncSecurity.queryValid_IND (p{1}, p{2}) ==>
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
      C.n{1} + C.q{1} = nwires /\
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
        do 12!(split; first by smt).
        split; first by move=> g b1 b2 g_bnd; cut:= H7 g _=> //; case b1; case b2 => /#.
        split; first by move=> g b1 b2 g_bnd; cut:= H18 g _; [idtac=>/#|]; case b1; case b2.
        by idtac=>/#.
    conseq (_: _ ==>
      (forall j,
        C.n{2} + C.q{2} - C.m{2} <= j < C.n{2} + C.q{2} =>
        C.v{1}.[j] = C.v{2}.[j]) /\
        size C.v{1} = C.n{2} + C.q{2} /\
        size C.v{2} = C.n{2} + C.q{2} /\
        (forall j, 0 <= j < C.n{2} => C.v{1}.[j] = C.x{1}.[j]) /\
        (forall j, 0 <= j < C.n{2} => C.v{2}.[j] = C.x{2}.[j])).
          progress; expect 3 by idtac=>/#.
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
            case ((i = j){2}) => hj; rewrite get_sub; smt ["Alt-Ergo"] tmo=10. 
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
        by case (useVisible{hr} && C.v{hr}.[j]); rewrite //= oget_some //=; smt full tmo=5. 
      case (j < i{hr})=> h.
        by rewrite !get_set_neq; expect 3 by idtac=>/#.
        cut ->: i{hr} = j by idtac=>/#.
        rewrite !getP /=.
        by case (useVisible{hr} && C.v{hr}.[j]); rewrite //= oget_some //=; smt full tmo=5.
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
            by (rewrite get_set; first by idtac=>/#); rewrite xorC xor_true //=; smt full tmo=10.
            by (rewrite get_set; first by idtac=>/#); rewrite xorC xor_false //=; smt full tmo=10.
          by cut:= H3 j v0; smt.
        by rewrite !getP => /#. 
        by rewrite !getP => /#. 
        by rewrite !getP; case (i{2} = j)=> h;[subst=> /= |cut := H4 j]; smt.
        by rewrite !getP; case (i{2} = j)=> h;[ |cut := H4 j]; smt.
    (wp; skip; progress=> //; simplify validRand validRand; first by idtac=>/#); last 8 by idtac=>/#. 
      by rewrite size_offun max_ler => /#.
      by rewrite size_offun max_ler => /#.
  qed.
  
  lemma sch_is_pi: EncSecurity.pi_sampler_works ().
  proof.
    rewrite /EncSecurity.pi_sampler_works=> plain.
    simplify validCircuit validInputs EncSecurity.Encryption.valid_plain EncSecurity.Encryption.leak EncSecurity.Encryption.pi_sampler pi_sampler phi eval.
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
     by move : hplain; simplify valid_circuit fst snd => /#.
     by rewrite size_offun max_ler => /#. 
qed.

  (**************)
    (** Game Real *)
    (**************)

(**
  GarbleInitReal module
*)
(** Initialises the garbling values of Game Real *)
module GarbleRealInit = {
    
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
    var tok : word;

    G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
    G.pp = map0;
    G.randG = map0;
    G.a = 0;
    G.b = 0;

    G.g = C.n;
    while (G.g < C.n + C.q)
    {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
        
      garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
        
      tok = garb'(false,  true, false);
      tok = garb'(false, false,  true);
      G.yy.[G.g] = garb'(false,  true,  true);
        
      G.g = G.g + 1;
    }
  }
}.

module GameReal (ADV:EncSecurity.Adv_IND_t) = {
      
  proc garble () : bool = {
    var query : Sec.EncSecurity.query_IND;
    var p : Sec.EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query = ADV.gen_query();
      
    if (EncSecurity.queryValid_IND query) {
      real = ${0,1};
      p = if real then snd query else fst query;
      CircuitInit.init(p);
      RandomInit.init(true);
      GarbleRealInit.init();
        
      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
          
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = $DBool.dbool;
    }

    return ret;
  }
}.

module type Scheme_t = {
  proc enc(p:fun_t*input_t) : funG_t*inputG_t*outputK_t { }
}.

module Game(S:Scheme_t, ADV:EncSecurity.Adv_IND_t) = {
  proc main() : bool = {
    var query,p,c,b,adv,ret;

    query = ADV.gen_query();
    if (EncSecurity.queryValid_IND query) {
      b = ${0,1};
      p = if b then snd query else fst query;
      c = S.enc(p);
      adv = ADV.get_challenge(c);
      ret = (b = adv);
    }
    else {
      ret = ${0,1};
    }
    return ret;
  }
}.

(* Gb from figure 7 *)
module Garble1 : Scheme_t = {
  proc enc(p:fun_t*input_t) : funG_t*inputG_t*outputK_t = {
    CircuitInit.init(p);
    RandomInit.init(false);
    return (funG C.f R.xx, encode (inputK C.f R.xx) C.x, outputK C.f R.xx);
  }
}.

(*****************************************************)
(* Lemmas concerning the PrivInd ~ GameReal equality *)
(*****************************************************)

lemma eqDefs (A<:EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}):
  equiv[Game(Garble1,A).main ~ EncSecurity.Game_IND(Rand,A).main:
  ={glob A} ==> ={res}].
proof.
  proc; inline Game(Garble1,A).main.
  swap{2} 1 1; seq 1 1: (={query, glob A}); first by call (_: true).
  case (EncSecurity.queryValid_IND query{1}); last by rcondf{1} 1=> //; rcondf{2} 2; auto; smt.
  rcondt{1} 1=> //; rcondt{2} 2; first by auto.
  inline*; wp; call (_: true); wp.
  while (useVisible{1}= false /\ i0{1} = i{2} /\
    (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst (if b{1} then snd query{1} else fst query{1})) /\
    C.n{1} = n{2} /\ C.m{1} = m{2} /\ C.q{1} = q{2} /\
    C.aa{1} = aa{2} /\ C.bb{1} = bb{2} /\ ={glob A, R.xx}).
      by auto. 
  wp; while{1} (true) ((C.n + C.q - i){1}); first by auto; smt.
  by auto; progress => /#. 
qed.

lemma equivRealInd_aux (A <: EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameReal(A).garble ~ Game(Garble1,A).main : ={glob A} ==> ={res} ].
proof.  
  move => AgenL AgetL.
  proc.
  seq 1 1 : (={query} /\ ={glob A}).
    by call (_ : true) => //; auto; smt.
  if; first by progress.
    wp; call (_ : true) => //; wp.
    inline Garble1.enc GarbleRealInit.init.
    while{1} (={glob A} /\ t_xor (C.n{1} + C.q{1}) R.t{1} R.t{2} C.v{1} /\
      0 <= C.q{2} /\
      C.n{2} <= G.g{1} /\
      C.f{2} = ((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2}) /\ valid_circuitP bound C.f{2} /\
      let (topo, gg) = funG C.f{2} R.xx{2} in
        ={glob C} /\
        (forall i v, 0 <= i < C.n + C.q => getlsb (oget R.xx.[(i, v)]) = v ^^ R.t.[i]){2} /\
        (forall g u, 0 <= g < (C.n + C.q){1} => R.xx.[(g, u)]{1} = R.xx.[(g, u)]{2}) /\
        (forall i, C.n <= i < C.n + C.q =>
          C.v{2}.[i] = oget C.gg.[(i, false ^^ C.v{2}.[C.aa{2}.[i]], false ^^ C.v{2}.[C.bb.[i]])]){2} /\
        topo = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
        G.g{1} <= C.n{1} + C.q{1} /\
        (forall i a b, !(G.g{1} <= i < C.n{1} + C.q{1}) => gg.[(i, a, b)] = G.pp{1}.[(i, a, b)]))
        ((C.n + C.q - G.g){1}).
          move => &m z.
          inline GarbleRealInit.garb' GarbleRealInit.garb.
          swap 13 -12.
          swap 26 -25.
          swap 39 -38.
          wp; simplify; do 3 ! rnd; skip.
          simplify funG funG fst snd t_xor. 
          (progress;first 2 by idtac=>/#);last 4 by smt.
            case (G.g{hr} = i)=> hi.
              rewrite hi !getP get_initGates; first idtac=>/#.
              cut -> /=: C.n{m} <= i < C.n{m} + C.q{m} by idtac=>/#.
              rewrite !xor_true !xor_false /=.
              cut hneq : forall (x:bool), ((! x) = x) = false by idtac=>/#.
              cut lem : forall u v, Some (enc R.xx{m} ((C.n{m}, C.m{m}, C.q{m}, C.aa{m}, C.bb{m}), C.gg{m}) i
              (u ^^ R.t{hr}.[C.aa{m}.[i]]) (v ^^ R.t{hr}.[C.bb{m}.[i]])) =
                Some (DKCSecurity.D.E (tweak i (R.t{hr}.[C.aa{m}.[i]]^^u) (R.t{hr}.[C.bb{m}.[i]]^^v))
                (oget R.xx{hr}.[(C.aa{m}.[i], u ^^ C.v{m}.[C.aa{m}.[i]])]) (oget R.xx{hr}.[(C.bb{m}.[i], v ^^ C.v{m}.[C.bb{m}.[i]])]) (oget R.xx{hr}.[(i, (oget C.gg{m}.[(i, u^^C.v{m}.[C.aa{m}.[i]], v^^C.v{m}.[C.bb{m}.[i]])]))])).
                move => u v.
                simplify enc fst snd.
                rewrite !H3;first 4 by elim H2 => /#.
                rewrite !H ;first 2 by elim H2 => /#. 
                rewrite !H4 ;first 3 by elim H2 => /#. 
                rewrite !(Bool.xorC false) !xor_false.
                cut xor_simpl : forall x y z, x ^^ (y ^^ z) ^^ y = x ^^ z
                  by (move => x y z;case x;case y;case z;do rewrite /= ?(xor_true, xor_false) //).
                rewrite !xor_simpl.
                by do 2 !congr; rewrite Bool.xorC; [rewrite (Bool.xorC u) | rewrite (Bool.xorC v)]; rewrite Bool.xorA.
            (case (a = R.t{hr}.[C.aa{m}.[i]])=> ha;[rewrite ? ha|cut -> : a = !R.t{hr}.[C.aa{m}.[i]] by idtac=>/#]);
            (case (b0 = R.t{hr}.[C.bb{m}.[i]])=> hb;[rewrite hb|cut -> : b0 = !R.t{hr}.[C.bb{m}.[i]] by idtac=>/#]);rewrite ?hneq /=.
              by (cut := lem false false;rewrite (H5 i) ?(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //; first by idtac=>/#) => /#. 
              by cut := lem false true; rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //; simplify; progress; (cut ->: R.t{hr}.[C.aa{m}.[i]] = ! R.t{hr}.[C.aa{m}.[i]] <=> false by idtac=>/#); simplify => /#.  
              by cut := lem true false;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //; simplify; progress; (cut ->: R.t{hr}.[C.bb{m}.[i]] = ! R.t{hr}.[C.bb{m}.[i]] <=> false by idtac=>/#); simplify => /#.  
              by cut := lem true true;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //.
              cut h : forall aa bb, ((G.g{hr}, R.t{hr}.[C.aa{m}.[G.g{hr}]] ^^ aa, R.t{hr}.[C.bb{m}.[G.g{hr}]] ^^ bb) = (i, a, b0)) = false by idtac=>/#.
            by rewrite !getP; simplify; (cut ->: i = G.g{hr} <=> false by idtac=>/#); simplify; apply H7 => /#. 
    wp.
    call RandomGenClassicVisibleE.
    call CircuitInitEquiv'.
    wp; rnd; skip.
    simplify funG funG fst.
    move => &1 &2 [[eq_query]] eq_adv valid.
    simplify validInputsP valid_circuitP fst snd.
    progress.
      by case realL => /#.
      by move : H1; case realL => /#.
      by move : H1; case realL => /#.     
      by move : H1; case realL => /#.
      by move : H1; case realL => /#.     
      by move : H1; case realL => /#. 
      by move : H1; case realL => /#. 
      by move : H1; case realL => /#. 
      by move : H1; case realL => /#. 
      move : valid; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP /fst /snd;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : valid; rewrite /queryValid_IND /valid_plain /validInputs /fst /snd ?valid_wireinput /valid_circuitP;
        case realL => /#. 
      by move : H1; case realL => /#.     
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by (rewrite get_initGates; first by idtac=>/#); rewrite H22 map0P //=.  
      by idtac=>/#.
      apply fmapP=> y; elim y=> i a b =>/#. 
    by auto.
          qed.

(*************)
(* Game Fake *)
(*************)

module GarbleInitFake = {

  proc garb(yy : word, alpha : bool, bet : bool) : unit = {
    var twe, aa, bb : word;
        
    twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ bet);
    aa = oget R.xx.[(G.a, C.v.[G.a] ^^ alpha)];
    bb = oget R.xx.[(G.b, C.v.[G.b] ^^ bet)];
    G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ bet)] = E twe aa bb yy;
  }

  proc garb'(rn : bool, alpha : bool, bet : bool) : word = {
    var yy : word;
        
    yy = $W.Dword.dword;
    yy = if rn then yy else oget R.xx.[(G.g, oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ bet)])];
    garb(yy, alpha, bet);
    return yy;
  }
    
  proc init() : unit = {
    var tok : word;

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
        
      tok = garb'(true, true,  false);
      tok = garb'(true,  false, true);
      G.yy.[G.g] = garb'(true,  true,  true);
      
      G.g = G.g + 1;
    }
  }
}.

module GameFake (ADV:EncSecurity.Adv_IND_t) = {
      
  proc garble () : bool = {
    var query : EncSecurity.query_IND;
    var p : EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query = ADV.gen_query();
        
    if (EncSecurity.queryValid_IND query) {
      real = ${0,1};
      p = if real then snd query else fst query;
      CircuitInit.init(p);
      RandomInit.init(true);
      GarbleInitFake.init();

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }
    
    return ret;
  }
}.

(**********************************************)
(* ALTERNATIVE VERSION - easy-independent one *)
(**********************************************)

module R' = {
  var t : bool array
  var vv : (int,word) fmap
  var ii : (int,word) fmap
}.

module RandomInit' = {
  proc init(useVisible:bool): unit = {
    var i, tok1, tok2, v, trnd;

    R'.t = offun (fun x, false) (C.n + C.q);
    R'.vv = map0;
    R'.ii = map0;

    i = 0;
    while (i < C.n + C.q) {
      trnd = ${0,1};
      v = if useVisible then C.v.[i] else false;
      trnd = if (i < C.n + C.q - C.m) then trnd else v;
      tok1 = $W.Dword.dwordLsb ( trnd);
      tok2 = $W.Dword.dwordLsb (!trnd);

      R'.t.[i] = trnd;

      R'.vv.[i] = tok1;
      R'.ii.[i] = tok2;

      i = i + 1;
    }
  } 
}.

module GarbleInitFake' = {
    
  proc init() : unit = {
    var tok : word;
    var wa, wb : word;
    var twe : word;
      
    G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
    G.pp = map0;
    G.randG = map0;
    G.a = 0;
    G.b = 0;

    G.g = C.n;
    while (G.g < C.n + C.q) {
      G.a = C.aa.[G.g];
      G.b = C.bb.[G.g];
        
      wa = oget R'.vv.[G.a];
      wb = oget R'.vv.[G.b];
      tok = oget R'.vv.[G.g];
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

      wa = oget R'.ii.[G.a];
      wb = oget R'.vv.[G.b];
      tok = $W.Dword.dword;
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
        
      wa = oget R'.vv.[G.a];
      wb = oget R'.ii.[G.b];
      tok = $W.Dword.dword;
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

      wa = oget R'.ii.[G.a];
      wb = oget R'.ii.[G.b];
      tok = $W.Dword.dword;
      twe = tweak G.g (getlsb wa) (getlsb wb);
      G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

      G.yy.[G.g] = tok;

      G.g = G.g + 1;
    }
  }
}.

module GameFake' (ADV:EncSecurity.Adv_IND_t) = {
  
  proc garble () : bool = {
    var query : EncSecurity.query_IND;
    var p : EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query = ADV.gen_query();
        
    if (EncSecurity.queryValid_IND query) {
      real = ${0,1};
      p = if real then snd query else fst query;
      CircuitInit.init(p);
      RandomInit'.init(true);
      GarbleInitFake'.init();

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), offun (fun g, oget (filter (fun a b, 0 <= a < C.n) R'.vv).[g]) C.n, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

module GameFake'' (ADV:EncSecurity.Adv_IND_t) = {
      
  proc garble () : bool = {
    var query : EncSecurity.query_IND;
    var p : EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query = ADV.gen_query();
        
    if (EncSecurity.queryValid_IND query) {
      real = ${0,1};
      p = fst query;
      CircuitInit.init(p);
      RandomInit'.init(true);
      GarbleInitFake'.init();

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), offun (fun g, oget (filter (fun a b, 0 <= a < C.n) R'.vv).[g]) C.n, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

lemma GarbleInitFakeL : islossless GarbleInitFake.init.
proof.
  proc.
  while true (C.n + C.q - G.g).
    progress; inline*; auto; simplify; smt.
  by auto => /#. 
qed.

equiv Random'InitEquiv: RandomInit'.init ~ RandomInit'.init:
  ={useVisible, C.n, C.m, C.q, C.aa, C.bb} /\
  (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
    C.v{1}.[i] = C.v{2}.[i]) /\
    (0 <= C.m <= C.n + C.q){1} /\
    useVisible{1} /\
    (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
    ={R'.t} /\
    (forall g, 0 <= g < (C.n + C.q){1} => R'.vv.[g]{1} = R'.vv.[g]{2}) /\
    (forall g, 0 <= g < (C.n + C.q){1} => R'.ii.[g]{1} = R'.ii.[g]{2}) /\
    (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{1}) = !getlsb (oget R'.ii.[g]{1})) /\
    (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{2}) = !getlsb (oget R'.ii.[g]{2})) /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){1} /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){2}.
proof.
  proc => //.
  while (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i} /\
    (forall (i0 : int),
      C.n{1} + C.q{1} - C.m{1} <= i0 < C.n{1} + C.q{1} =>
      C.v{1}.[i0] = C.v{2}.[i0]) /\
    0 <= C.m{1} <= C.n{1} + C.q{1} /\
    useVisible{1} /\
    fst C.f{1} = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
    0 <= i{1} <= C.n{1} + C.q{1} /\
    (forall (g : int), 0 <= g < i{1} => R'.vv{1}.[g] = R'.vv{2}.[g]) /\
    (forall (g : int), 0 <= g < i{1} => R'.ii{1}.[g] = R'.ii{2}.[g]) /\
    (forall (g : int), 0 <= g < i{1} => R'.t{1}.[g] = R'.t{2}.[g]) /\
    (forall (g : int), 0 <= g < i{1} => getlsb (oget R'.vv{1}.[g]) = !getlsb (oget R'.ii{1}.[g])) /\
    (forall (g : int), 0 <= g < i{1} => getlsb (oget R'.vv{2}.[g]) = !getlsb (oget R'.ii{2}.[g])) /\
    (0 <= C.m{1} <= C.n{1} + C.q{1} /\ size R'.t{1} = C.n{1} + C.q{1}) /\
    (0 <= C.m{2} <= C.n{2} + C.q{2} /\ size R'.t{2} = C.n{2} + C.q{2})).
      auto; progress; first 6 by idtac=>/#.
        rewrite ?getP => /#.
        rewrite ?getP => /#.
        rewrite ?get_set => /#.
        rewrite ?getP; case (g = i{2}) => hc; smt tmo=5.
        rewrite ?getP; case (g = i{2}) => hc; smt tmo=5.
        by rewrite size_set.
        by rewrite size_set.
    auto; progress; first 3 by idtac=>/#.
      by rewrite size_offun max_ler => /#.
      by rewrite size_offun max_ler => /#.
      by rewrite arrayP => /#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
  qed.  


  
equiv GarbleInitFake'InitEquiv: GarbleInitFake'.init ~ GarbleInitFake'.init:
  ={C.n, C.m, C.q, C.aa, C.bb} /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => R'.vv{1}.[k] = R'.vv{2}.[k]) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = getlsb (oget R'.vv{2}.[k])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => R'.ii{1}.[k] = R'.ii{2}.[k]) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.ii{1}.[k]) = getlsb (oget R'.ii{2}.[k])) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = !getlsb (oget R'.ii{1}.[k])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{2}.[k]) = !getlsb (oget R'.ii{2}.[k])) /\
  (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
    (forall g a b, C.n{1} <= g < (C.n + C.q){1} => G.pp.[(g,a,b)]{1} = G.pp.[(g,a,b)]{2}) /\
    (forall g a b, !(C.n{1} <= g < (C.n + C.q){1}) => G.pp.[(g,a,b)]{1} = None) /\
    (forall g a b, !(C.n{1} <= g < (C.n + C.q){1}) => G.pp.[(g,a,b)]{2} = None).
proof.
  proc => //.
  while (={C.n, C.m, C.q, C.aa, C.bb} /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => R'.vv{1}.[k] = R'.vv{2}.[k]) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => R'.ii{1}.[k] = R'.ii{2}.[k]) /\
    validInputsP (C.f{1}, C.x{1}) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = !getlsb (oget R'.ii{1}.[k])) /\
    (forall k, 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{2}.[k]) = !getlsb (oget R'.ii{2}.[k])) /\
    (forall (k : int), 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.vv{1}.[k]) = getlsb (oget R'.vv{2}.[k])) /\
    (forall (k : int), 0 <= k < C.n{1} + C.q{1} => getlsb (oget R'.ii{1}.[k]) = getlsb (oget R'.ii{2}.[k])) /\
    fst C.f{1} = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
    (forall (g : int) (a b : bool), C.n{1} <= g < G.g{1} => G.pp{1}.[(g, a, b)] = G.pp{2}.[(g, a, b)]) /\
    (forall g a b, C.n{1} <= g < G.g{1} => mem (dom G.pp{1}) (g,a,b)) /\
    (forall g a b, C.n{1} <= g < G.g{1} => mem (dom G.pp{2}) (g,a,b)) /\
    (forall g a b, g < C.n{1} => !mem (dom G.pp{1}) (g,a,b)) /\
    (forall g a b, G.g{1} <= g => !mem (dom G.pp{1}) (g,a,b)) /\
    (forall g a b, g < C.n{1} => !mem (dom G.pp{2}) (g,a,b)) /\
    (forall g a b, G.g{1} <= g => !mem (dom G.pp{2}) (g,a,b)) /\
    (forall g a b, g < C.n{1} => G.pp{1}.[(g, a, b)] = None) /\
    (forall g a b, G.g{1} <= g => G.pp{1}.[(g, a, b)] = None) /\
    (forall g a b, g < C.n{1} => G.pp{2}.[(g, a, b)] = None) /\
    (forall g a b, G.g{1} <= g => G.pp{2}.[(g, a, b)] = None) /\
    ={G.g} /\ C.n{1} <= G.g{1} <= C.n{1} + C.q{1}).
      auto; progress.
        rewrite ?getP //=. case (g = G.g{2}) => hc. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. simplify => /#. simplify. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. simplify =>/#. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify => /#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false by idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify => /#. simplify => /#. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. smt.

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. by simplify. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt. 

        rewrite in_dom. rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.
    
        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        rewrite ?getP. simplify. case (g = G.g{2}) => hc. simplify. case (a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) => ha. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. case (b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]])) => hb. idtac=>/#. cut ->: b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true by idtac=>/#. simplify. idtac=>/#. simplify. smt.

        by idtac=>/#.
        by idtac=>/#. 

    wp; skip; progress; first 2 by idtac=>/#. 
      by rewrite dom0 in_fset0.  
      by rewrite dom0 in_fset0.  
      by rewrite dom0 in_fset0.   
      by rewrite dom0 in_fset0.  
      by rewrite map0P. 
      by rewrite map0P. 
      by rewrite map0P. 
      by rewrite map0P. 
      by idtac=>/#. 
      by idtac=>/#. 
      by idtac=>/#. 
      by idtac=>/#. 
  qed.
  

equiv RandomInit_RandomInit' : RandomInit.init ~ RandomInit'.init:
  ={useVisible, C.n, C.m, C.q, C.aa, C.bb} /\
  (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
    C.v{1}.[i] = C.v{2}.[i]) /\
  (0 <= C.m <= C.n + C.q){1} /\
  useVisible{1} /\
  (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
    R.t{1} = R'.t{2} /\
    (forall g, 0 <= g < (C.n + C.q){1} => R.xx{1}.[(g, C.v{1}.[g])] = R'.vv{2}.[g]) /\
    (forall g, 0 <= g < (C.n + C.q){1} => R.xx{1}.[(g, !C.v{1}.[g])] = R'.ii{2}.[g]) /\
    (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = getlsb (oget R'.vv{2}.[k])) /\
    (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = !getlsb (oget R'.ii{2}.[k])) /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R.t = (C.n+C.q)){1} /\
    (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){2}.
proof.
  proc => //.
  seq 3 4 : (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i} /\
    (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} =>
      C.v{1}.[i] = C.v{2}.[i]) /\
    (0 <= C.m <= C.n + C.q){1} /\
    useVisible{1} /\
    (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} /\ R.t{1} = R'.t{2} /\
    R.t{1} = offun (fun (_ : int) => false) (C.n + C.q){2} /\
    size R.t{1} = (C.n + C.q){2} /\ R.xx{1} = map0 /\
    R'.vv{2} = map0 /\ R'.ii{2} = map0 /\ i{1} = 0).
      by auto; progress; expect 1 by rewrite size_offun max_ler => /#. 
  while (={useVisible, C.n, C.m, C.q, C.aa, C.bb, i} /\
    (forall (i0 : int),
      C.n{1} + C.q{1} - C.m{1} <= i0 < C.n{1} + C.q{1} =>
      C.v{1}.[i0] = C.v{2}.[i0]) /\
    0 <= C.m{1} <= C.n{1} + C.q{1} /\
    useVisible{1} /\
    fst C.f{1} = (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) /\
    R.t{1} = R'.t{2} /\
    size R.t{1} = C.n{2} + C.q{2} /\ size R'.t{2} = C.n{2} + C.q{2} /\
    (forall g, 0 <= g < i{1} => R.xx{1}.[(g, C.v{1}.[g])] = R'.vv{2}.[g]) /\
    (forall g, 0 <= g < i{1} => R.xx{1}.[(g, !C.v{1}.[g])] = R'.ii{2}.[g]) /\
    (forall k, 0 <= k < i{1} => R.t{1}.[k] = getlsb (oget R'.vv{2}.[k])) /\
    (forall k, 0 <= k < i{1} => R.t{1}.[k] = !getlsb (oget R'.ii{2}.[k]))).
      auto; progress; first 5 by idtac=>/#.
        by rewrite size_set.
        by rewrite size_set.
        rewrite ?getP H2 //= /#. 
        rewrite ?getP H2 //= /#. 
        rewrite ?getP ?get_set; first by idtac=>/#. rewrite H2 //=. case (i{2} < C.n{2} + C.q{2} - C.m{2}) => hi. case (k = i{2}) => hk. rewrite oget_some; first by smt. idtac=>/#. case (k = i{2}) => hk; first by smt. idtac=>/#.
        rewrite ?getP ?get_set; first by idtac=>/#. rewrite H2 //=. case (i{2} < C.n{2} + C.q{2} - C.m{2}) => hi. case (k = i{2}) => hk. rewrite oget_some; first by smt. idtac=>/#. case (k = i{2}) => hk; first by smt. idtac=>/#.
  by auto; progress => /#. 
qed.

lemma same_fakes (A<:EncSecurity.Adv_IND_t{C,R,R',G}):
  equiv[GameFake(A).garble ~ GameFake'(A).garble : ={glob A} ==> ={res}].
proof.
  proc => //.
  seq 1 1 : (={glob A, query}).
    by call (_ : true).
  if; first by progress.
    wp; call (_ : true); wp.
    inline GarbleInitFake.init GarbleInitFake'.init.
    while (={p, real, glob A, query, C.n, C.m, C.q, C.aa, C.bb, C.gg, G.g, C.v} /\ R.t{1} = R'.t{2} /\
      EncSecurity.queryValid_IND query{1} /\
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,C.v{1}.[k])] = R'.vv{2}.[k]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,!C.v{1}.[k])] = R'.ii{2}.[k]) /\
      (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = getlsb (oget R'.vv{2}.[k])) /\
      (forall k, 0 <= k < (C.n + C.q){1} => R.t{1}.[k] = !getlsb (oget R'.ii{2}.[k])) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).
      inline*; auto; progress; first 2 by idtac=>/#.

        rewrite ?getP ?xor_false ?xor_true //=.
        case (k = G.g{2}) => hk. case (a = ! R'.t{2}.[C.aa{2}.[G.g{2}]]) => ha. case (b = ! R'.t{2}.[C.bb{2}.[G.g{2}]]) => hb.
        cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] <=> false by idtac=>/#.
        cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] <=> false by idtac=>/#.

        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> true. simplify. rewrite ha. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. 
        cut ->: b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true. simplify. rewrite hb. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done.

        simplify. 

        congr. congr. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite H6. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H4. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. rewrite H4. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done.

        simplify. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify.  
        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. rewrite ha. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = ! getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. 

        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true. simplify. rewrite ha. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. rewrite -H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.
        cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. simplify. rewrite ha. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.

        simplify.

        congr. congr. cut ->: (! R'.t{2}.[C.aa{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> R'.t{2}.[C.aa{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) by idtac=>/#. rewrite H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#.  done. cut ->: R'.t{2}.[C.bb{2}.[G.g{2}]] = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H4; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H3; first rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.

        simplify.

        case (b = ! R'.t{2}.[C.bb{2}.[G.g{2}]]) => hb. simplify. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. 

        cut ->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. simplify. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. rewrite hb. rewrite H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. by cut ->: (! getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]])) = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) <=> false by idtac=>/#. 
        cut ->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> true. simplify. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. rewrite hb. rewrite -H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = !getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. by rewrite -H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. 

        simplify.

        congr. congr. rewrite H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. cut ->: (! R'.t{2}.[C.bb{2}.[G.g{2}]]) = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> R'.t{2}.[C.bb{2}.[G.g{2}]] = ! getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) by idtac=>/#. rewrite -H6; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#.  done. congr. rewrite H3; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H4; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.

        simplify.

        cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] && b = R'.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. 
        cut->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H6; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.
        
        cut->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) <=> false. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H6; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.
 
        cut->: a = getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> false. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H6; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. idtac=>/#.

        cut->: a = getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) && b = getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) <=> true. cut ->: a = R'.t{2}.[C.aa{2}.[G.g{2}]] by idtac=>/#. cut ->: b = R'.t{2}.[C.bb{2}.[G.g{2}]] by idtac=>/#. rewrite ?H5; first 2 by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. 

         simplify.

         congr. congr. rewrite H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. rewrite H5; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. rewrite H3; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done. congr. rewrite H3; first by rewrite -?H5; first by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. done.

        rewrite ?getP ?xor_false ?xor_true //= /#.
        simplify; rewrite ?getP ?xor_false ?xor_true //= /#.
        rewrite ?getP ?xor_false ?xor_true //= /#. 
        rewrite ?getP ?xor_false ?xor_true //= /#.    
        rewrite ?getP ?xor_false ?xor_true //= /#.   
        rewrite ?getP ?xor_false ?xor_true //= /#.     

      wp; call RandomInit_RandomInit'; call CircuitInitEquiv'.
      auto; progress. 
        by case realL => hr; move : H; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput; simplify validInputsP. 
        by idtac=>/#.
        by idtac=>/#.              
        by idtac=>/#.
        by rewrite map0P.        
        by rewrite map0P.
        by rewrite map0P.
        by rewrite map0P.
        rewrite fmapP => x; elim x => k a b => /#.
        simplify encode. congr. rewrite fun_ext /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hx. case (mem (dom xx_L) (x, x_R.[x])) => hxx. cut ? : xx_L.[(x, x_R.[x])] <> None by rewrite -in_dom. cut ? : vv_R.[(x)] <> None by rewrite -H26 => /#. cut ->: mem (dom vv_R) x <=> true by rewrite in_dom. simplify. idtac=>/#. cut ? : xx_L.[(x, x_R.[x])] = None by smt. cut ? : vv_R.[(x)] = None by rewrite -H26 => /#. cut ->: mem (dom vv_R) x <=> false by smt. by simplify. by simplify.
        by idtac=>/#.
    by auto.
qed.


lemma GameFake'_GameFake'' (A<:EncSecurity.Adv_IND_t{C,R,R',G}) &m :
  equiv[GameFake'(A).garble ~ GameFake''(A).garble : ={glob A} ==> ={res}].
proof.
  proc.
  seq 1 1 : (={glob A, query}).
    call (_ : true) => //.
  if; first by progress.
    wp; call (_ : true); wp.
    seq 4 4 : (
      (={glob A, query, real, C.n, C.m, C.q, C.aa, C.bb} /\
      (forall i, C.n{1} + C.q{1} - C.m{1} <= i < C.n{1} + C.q{1} => C.v{1}.[i] = C.v{2}.[i]) /\
      (eval C.f C.x){1} = (eval C.f C.x){2} /\
      (((C.n, C.m, C.q, C.aa, C.bb), C.gg) = C.f /\
        Array.size C.v = (C.n + C.q) /\
        validInputsP (C.f, C.x)){1} /\
      (forall i, 0 <= i < C.n{1} => C.v{1}.[i] = C.x{1}.[i]) /\
      (((C.n, C.m, C.q, C.aa, C.bb), C.gg) = C.f /\
        Array.size C.v = (C.n + C.q) /\
        validInputsP (C.f, C.x)){2} /\
      (forall i, 0 <= i < C.n{1} => C.v{2}.[i] = C.x{2}.[i])) /\
      ={R'.t} /\
      (forall g, 0 <= g < (C.n + C.q){1} => R'.vv.[g]{1} = R'.vv.[g]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => R'.ii.[g]{1} = R'.ii.[g]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{1}) = !getlsb (oget R'.ii.[g]{1})) /\
      (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{2}) = !getlsb (oget R'.ii.[g]{2})) /\
      (0 <= C.m <= C.n + C.q /\
        Array.size R'.t = (C.n+C.q)){1}).    

        call Random'InitEquiv.
        call InitEquiv_rnd.
        auto; progress; first 4 by idtac=>/#.
          by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
          by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
    call GarbleInitFake'InitEquiv.
    auto; progress; first 2 by idtac=>/#. 
      by apply fmapP; rewrite /(==) => x; elim x => g a b => /#. 
      congr. apply fun_ext; rewrite /(==) => x. congr. rewrite ?filterP. simplify. case (0 <= x < C.n{2}) => hc; last by done. simplify. cut ? : C.n{2} < C.n{2} + C.q{2}. move : H2. simplify validInputsP valid_circuitP fst snd => /#. rewrite ?H7. idtac => /#. congr. smt. 
    by auto.
qed.

lemma GameFake''_independent (A<:EncSecurity.Adv_IND_t{C,R,R',G}) &m :
  islossless A.gen_query =>
  islossless A.get_challenge =>
  Pr[GameFake''(A).garble() @ &m: res] = 1%r / 2%r.
proof.
  move => AgenLL AgetLL.
  byphoare => //; proc.
  seq 1 : true (1%r) (1%r/2%r) (0%r) _ true => //; first by call (_ : true).
  if; last by rnd; skip; smt. 
    wp.
    swap 1 6.
    rnd ((=) adv).
    conseq (_ : true) =>//; first by progress;case adv0;smt. 
    call (_ : true) => //.
    wp. 
    inline GarbleInitFake'.init.
    while (true) (C.n + C.q - G.g).
      auto; progress; expect 2 by smt.
    auto. 
    inline RandomInit'.init.
    while true (C.n + C.q - i).
      auto; progress; expect 4 by smt.  
    auto.
    inline CircuitInit.init.
    while true (C.n + C.q - i0).
      auto; progress; expect 1 by idtac=>/#.
    auto; progress => /#.
qed.


lemma GameFake_independent (A<:EncSecurity.Adv_IND_t{C,R,R',G}) &m :
  islossless A.gen_query =>
  islossless A.get_challenge =>
  Pr[GameFake(A).garble() @ &m: res] = 1%r / 2%r.
proof.
  move => AgenL AgetL.
  rewrite -(GameFake''_independent A &m AgenL AgetL).
  cut <-: Pr[GameFake'(A).garble() @ &m : res] = Pr[GameFake''(A).garble() @ &m : res] by
    byequiv (GameFake'_GameFake'' A &m).
  by byequiv (same_fakes A).
qed.

(***************)
(* Game Hybrid *)
(***************)

module GarbleHybridInit = {

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
    
  proc init(l : int) : unit = {
    var tok : word;

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
        
      tok = garb'(G.a <= l, true,  false);
      tok = garb'(G.b <= l,  false, true);
      G.yy.[G.g] = garb'(G.a <= l,  true,  true);
        
      G.g = G.g + 1;
    }
  }
}.

module GameHybrid (ADV:EncSecurity.Adv_IND_t) = {
      
  proc garble (l : int) : bool = {
    var query : EncSecurity.query_IND;
    var p : EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
      
    query = ADV.gen_query();
        
    if (EncSecurity.queryValid_IND query) {
      real = ${0,1};
      p = if real then snd query else fst query;
      CircuitInit.init(p);
      RandomInit.init(true);
      GarbleHybridInit.init(l);

      c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
        
      adv = ADV.get_challenge(c);
      ret = (real = adv);
    }
    else {
      ret = ${0,1};
    }

    return ret;
  }
}.

equiv RinitE:
  RandomInit.init ~ RandomInit.init:
    ={useVisible, glob C} /\
    (0 <= C.m <= C.n + C.q){1} /\
    (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
      ={glob R} /\
      (validRand C.f R.xx){1} /\
      (Array.size R.t = (C.n+C.q)){1}.
proof. by conseq (_: ={useVisible,glob C} ==> ={glob R}) RandomInitH; sim. qed.
  
lemma GameReal_GameHybrid0 (A <: EncSecurity.Adv_IND_t{Rand,R,GameReal,GameHybrid}): 
  islossless A.gen_query =>
  islossless A.get_challenge => 
  equiv [GameReal(A).garble ~ GameHybrid(A).garble : ={glob A} /\ l{2} = -1 ==> ={res}].
proof.
  move => AgenL AgetL.
  proc.
  seq 1 1 : (={glob A, query} /\ l{2} = -1).
    by call (_ : true).
  (if; first by progress); last by auto.
    wp.
    call (_ : true) => //.
    wp.
    inline GarbleRealInit.init GarbleHybridInit.init. 
    while (={p, real, glob A, query, C.n, C.m, C.q, C.aa, C.bb, C.gg, G.g, C.v} /\ ={R.t} /\
      EncSecurity.queryValid_IND query{1} /\
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      l{2} = -1 /\
      l0{2} = l{2} /\
      (forall k b, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,b)] = R.xx{2}.[(k,b)]) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).

      inline*; auto. progress. 
      by idtac=>/#.
      by idtac=>/#.  

      cut ->: C.aa{2}.[G.g{2}] <= -1 <=> false by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= =>/#. cut ->: C.bb{2}.[G.g{2}] <= -1 <=> false by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= =>/#. simplify. rewrite ?getP ?xor_true ?xor_false. simplify. case (k = G.g{2}) => hc. simplify. case (a = !R.t{2}.[C.aa{2}.[G.g{2}]]) => ha. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. cut ->: a = R.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. rewrite H4. idtac=> /#. done.
    
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    wp; call RandomInitEquiv; call CircuitInitEquiv'.
    auto; progress.    
      by move : H; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=; case realL => /#. 
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      apply fmapP; rewrite /(==) => x; elim x => k a b => /#. 
      simplify encode; congr; apply fun_ext; rewrite /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hc. rewrite H22; first by idtac => /#. smt. done.   
qed.

(**************************************************************)
(* Lemmas concerning the GameHybrid_bound ~ GameFake equality *)
(**************************************************************)

lemma GameFake_GameHybridBound (A <: EncSecurity.Adv_IND_t{Rand,R,GameReal,GameHybrid}): 
  islossless A.gen_query =>
  islossless A.get_challenge => 
equiv [GameFake(A).garble ~ GameHybrid(A).garble : ={glob A} /\ l{2} = bound-1 ==> ={res}].
proof.
  move => AgenL AgetL.
  proc.
  seq 1 1 : (={glob A, query} /\ l{2} = bound-1).
    by call (_ : true).
  (if; first by progress); last by auto.
    wp.
    call (_ : true) => //.
    wp.
    inline GarbleInitFake.init GarbleHybridInit.init. 
    while (={p, real, glob A, query, C.n, C.m, C.q, C.aa, C.bb, C.gg, G.g, C.v} /\ ={R.t} /\
      EncSecurity.queryValid_IND query{1} /\
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      l{2} = bound-1 /\
      l0{2} = l{2} /\
      (forall k b, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,b)] = R.xx{2}.[(k,b)]) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).

      inline*; auto; progress.
      by idtac=>/#.
      by idtac=>/#.

      cut ->: C.aa{2}.[G.g{2}] <= SomeGarble.bound - 1 <=> true by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. cut ->: C.bb{2}.[G.g{2}] <= SomeGarble.bound - 1 <=> true by move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //= /#. simplify. rewrite ?getP ?xor_true ?xor_false. simplify. case (k = G.g{2}) => hc. simplify. case (a = !R.t{2}.[C.aa{2}.[G.g{2}]]) => ha. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. case (b = !R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. congr. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. case (b = ! R.t{2}.[C.bb{2}.[G.g{2}]]) => hb. cut ->: a = R.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. cut ->: a = R.t{2}.[C.aa{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. cut ->: b = R.t{2}.[C.bb{2}.[G.g{2}]] <=> true by idtac=>/#. simplify. congr. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. congr. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. rewrite H3. move : H0; rewrite /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=. idtac=>/#. done. simplify. rewrite H4. idtac=> /#. done.

    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    rewrite ?getP => /#. 
    wp; call RandomInitEquiv; call CircuitInitEquiv'.
    auto; progress.
      by move : H; rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /validInputsP ?valid_wireinput /valid_circuitP /fst /snd //=; case realL => /#.  
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by idtac=>/#.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      by rewrite map0P.
      apply fmapP; rewrite /(==) => x; elim x => k a b => /#. 
      simplify encode. congr. apply fun_ext. rewrite /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < n_R) => hc. rewrite H22; first by idtac => /#. smt. done. 
qed.

(*************************************************)
(* Lemmas concerning probabilities of GameHybrid *)
(*************************************************)

lemma GameHybrid0_Game_IND_pr (A <: EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>  
  Pr[GameHybrid(A).garble((-1)) @ &m :res] = Pr[EncSecurity.Game_IND(Rand,A).main()@ &m:res].
proof.
  move => AgenL AgetL.
  cut <-: Pr[Game(Garble1,A).main()@ &m :res] = Pr[EncSecurity.Game_IND(Rand,A).main()@ &m:res]
    by byequiv (eqDefs A).
  cut <-: Pr[GameReal(A).garble()@ &m:res] = Pr[Game(Garble1,A).main()@ &m :res]
    by byequiv (equivRealInd_aux A AgenL AgetL).      
  cut ->: Pr[GameHybrid(A).garble(-1) @ &m : res] = Pr[GameReal(A).garble() @ &m : res] <=>
    Pr[GameReal(A).garble() @ &m : res] = Pr[GameHybrid(A).garble(-1) @ &m : res] by idtac=>/#.
  by byequiv (GameReal_GameHybrid0 A AgenL AgetL). 
qed.

lemma GameHybridBound_independent (A <: EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,R',C}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>  
  Pr[GameHybrid(A).garble(bound - 1)@ &m:res] = 1%r / 2%r.
proof.
  move => AgenL AgetL.
  rewrite -(GameFake_independent A &m) //=.
  cut ->: Pr[GameHybrid(A).garble(bound - 1) @ &m : res] = Pr[GameFake(A).garble() @ &m : res] <=> Pr[GameFake(A).garble() @ &m : res] = Pr[GameHybrid(A).garble(bound - 1) @ &m : res] by idtac=>/#.
  by byequiv (GameFake_GameHybridBound A AgenL AgetL).
qed.

lemma GameHybridBound_pr (A <: EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,R',C}) &m:
  islossless A.gen_query =>
  islossless A.get_challenge =>  
  2%r * Pr[GameHybrid(A).garble(bound - 1)@ &m:res] = 1%r.
proof. by move => AgenL AgetL; rewrite (GameHybridBound_independent A &m) //. qed.

  (***********)
  (* DKC ADVERSARY *)
  (*********)

(** 'l' parameter and its position *)
  (*op l : int.
  axiom l_pos : 0 <= l < bound.*)

  module AdvInit (D : DKC_t) = {
    
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

      R.t.[DKCp.l] = !lsb;
    }
    
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
  
  proc garble() : unit = {
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

      if (!(G.a < DKCp.l)) {
         query_garble(false, false);
         query_garble(true, false);
         query_garble(false, true);
         query_garble(true, true);
      }

      else {
        if ((G.a < DKCp.l) /\ !(G.b < DKCp.l)) {
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

module DKC_Adv (D : DKC_t, Adv_IND : EncSecurity.Adv_IND_t) : Adv_DKC_t = {

  proc get_l() : int = {
    return DKCp.l;
  }
  
  proc get_challenge (lsb:bool, l : int) : bool = {
    var query_ind : EncSecurity.query_IND;
    var p : EncSecurity.Encryption.plain;
    var ret : bool;
    var topo : topo_t;
    var real, adv : bool;
    var c : funG_t*inputG_t*outputK_t;
    var i : int;
    var ki,kj,zz,twe : word;
    
    query_ind = Adv_IND.gen_query();
      
    if (EncSecurity.queryValid_IND query_ind) {
      real = ${0,1};
      p = if real then snd query_ind else fst query_ind;
      CircuitInit.init(p);
      AdvInit(D).init(true, lsb);
      AdvInit(D).garble();

      i = 0;
      while (i < C.n) {
        twe = tweak i C.x.[i] R.t.[0]; 
        (ki,kj,zz) = D.encrypt(false, (i, R.t.[i]), (C.n+C.q-1, R.t.[DKCp.l]), (C.n+C.q, R.t.[0]), twe);
        R.xx.[(i, C.x.[i])] = ki;
        i = i + 1;
      }
      
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

lemma DKC_Adv_query_garble_ll (A <: EncSecurity.Adv_IND_t{Rand,R,C,DKC_Adv,DKCp}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless AdvInit(DKC).query_garble.
proof.
  move => Agen_ll Aget_ll.
  proc.
  by wp; call encrypt_ll; wp.
qed.

lemma DKC_Adv_query_garble_dummy_ll (A <: EncSecurity.Adv_IND_t{Rand,R,C,DKC_Adv,DKCp}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless AdvInit(DKC).query_garble_dummy.
proof.
  move => Agen_ll Aget_ll.
  proc.
  by wp; call encrypt_ll; wp.
qed.

lemma DKC_Adv_get_ll (A <: EncSecurity.Adv_IND_t{Rand,R,C,DKC_Adv,DKCp}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless DKC_Adv(DKC, A).get_challenge.
proof.
  move => Agen_ll Aget_ll.
  proc => //.
  seq 1 : true => //; first by call (_:true).
  if.
  wp; call (_:true) => //; wp; while true (C.n - i).
      by move => z; auto; call encrypt_ll; auto => /#. 
  wp.
  
  call (_: 0 <= C.n /\ 0 <= C.q ==> true) => //.
  proc.


    while (0 <= C.n /\ 0 <= C.q /\ C.n <= G.g <= C.n + C.q) (C.n + C.q - G.g).
  progress.
  case (! C.aa.[G.g] < DKCp.l). rcondt 3. by auto.
  wp. 
    call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  auto. progress => /#.
  rcondf 3. by auto.
  case (C.aa.[G.g] < DKCp.l /\ ! C.bb.[G.g] < DKCp.l). rcondt 3. by auto.
wp. 
    call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  auto. progress => /#.

rcondf 3. by auto.
wp. 
    call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  call (_ : true). by wp; call encrypt_ll; wp.
  auto. progress => /#.
wp. skip. progress => /#. 

  call (_ : true) => //.

  wp. while true (C.n + C.q - i).
    progress. auto. smt.
  by auto; smt.

  inline CircuitInit.init.
  while (EncSecurity.queryValid_IND query_ind /\
   p = if real then snd query_ind else fst query_ind) (C.n + C.q - i0).
  progress.
  auto; smt.
  auto; progress.
  smt. case (real{hr}) => hc.
  move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress. idtac=>/#.
  move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress. idtac=>/#.


  case v => hv. move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress.  idtac=>/#. move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress.  idtac=>/#.
  case v => hv. move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress.  idtac=>/#. move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress.  idtac=>/#.
  move : H. simplify EncSecurity.queryValid_IND EncSecurity.Encryption.valid_plain validInputs. rewrite ?valid_wireinput. simplify valid_circuitP. simplify fst snd. elim (query_ind{hr}.`1.`1.`1) => n m q aa bb. elim (query_ind{hr}.`2.`1.`1) => n' m' q' aa' bb'. simplify. progress. idtac=>/#.
  by auto; smt.
qed.

(*lemma GameHybrid_l1_sim (A <: EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}):
  islossless A.gen_query =>
  islossless A.get_challenge =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ (forall (plain:fun_t*input_t), let (n,m,q,aa,bb) = fst (fst plain) in DKCSecurity.bound = n + q) /\ DKCSecurity.l = l /\ DKCSecurity.boundl = bound /\ l{1} = l-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} ==> ={res}].*)

lemma GameHybrid_l1_sim (A <: EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}) lp:
  islossless A.gen_query =>
  islossless A.get_challenge =>
  0 <= lp < boundl =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ l{1} = lp-1 /\ l{2} = lp /\ b{2} ==> ={res}].
proof.
 move => Agen_ll Aget_ll hl.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  swap{2} 16 -15.
  seq 1 1 : (={glob A} /\ l{1} = lp - 1 /\ l{2} = lp /\ b{2} /\ query{1} = query_ind{2}); first by call (_ : true).

  case (EncSecurity.queryValid_IND query{1}).
    rcondt{1} 1; first by progress.
    rcondt{2} 16. auto. while (true). auto. wp. while (true). auto. by auto. 
    swap{2} 16 -15.
    swap{2} 17 -15.
    swap{2} 18 -15.
    seq 3 3 : ((={glob A,real,p} /\
      query{1} = query_ind{2} /\ 
      l{1} = lp-1 /\ l{2} = lp /\ b{2}) /\
      EncSecurity.queryValid_IND query{1} /\ ={glob C} /\
      size C.v{1} = (C.n + C.q){1} /\
      C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
      validInputsP (C.f, C.x){1} /\
      (forall i, 0 <= i < C.n{2} => C.v{2}.[i] = C.x{2}.[i]) /\
      (forall i, C.n <= i < C.n + C.q => C.v{2}.[i] = oget C.gg.[(i, C.v{2}.[C.aa{2}.[i]], C.v{2}.[C.bb.[i]])]){2}).
      call CircuitInitEquiv'.
      auto; progress. 
        by move : H0; rewrite /queryValid_IND /valid_plain /validInputs /validInputsP ?valid_wireinput /valid_circuitP /fst /snd; case realL. 
        (*by simplify validBound; case realL => /#.*)

    seq 1 16 : (={glob A, real, p} /\
      query{1} = query_ind{2} /\
      l{1} = lp-1 /\ l{2} = lp /\ DKCp.l{2} = l{2} /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\
      EncSecurity.queryValid_IND query{1} /\ 
      ={glob C} /\ 
      size C.v{1} = C.n{1} + C.q{1} /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
      (forall (i0 : int), 0 <= i0 < C.n{2} => C.v{2}.[i0] = C.x{2}.[i0]) /\
      (forall (i0 : int),
        C.n{2} <= i0 < C.n{2} + C.q{2} =>
        C.v{2}.[i0] =
        oget C.gg{2}.[(i0, C.v{2}.[C.aa{2}.[i0]], C.v{2}.[C.bb{2}.[i0]])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
      R.t{2}.[lp] = !DKCp.lsb{2} /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> lp => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
        oget R.xx{1}.[(lp, !C.v{1}.[lp])] = DKCp.ksec{2} /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)).
    
      inline RandomInit.init AdvInit(DKC).init.

      transitivity{2} {
        b0 = b;
        l0 = l;
    
        DKCp.lsb = witness;
        DKCp.ksec = witness;
        DKCp.b = b0;
        DKCp.l = l0;
        DKCp.used = fset0;
        DKCp.kpub = map0;
      
        i = 0;

        while (i < C.n + C.q) {
          DKCp.kpub.[(i, false)] = W.zeros;
          DKCp.kpub.[(i, true)] = W.zeros;
          i = i + 1;
        }
      
        i = 0;
        while (i < C.n + C.q) {
          if (i = lp) {
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
        R.t.[DKCp.l] = !DKCp.lsb;
      }
      ( (={glob A, real, p} /\
          query{1} = query_ind{2} /\
          l{1} = lp-1 /\ b{2} /\ l{2} = lp) /\
        EncSecurity.queryValid_IND query{1} /\
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

        ={glob A, real, p} /\
        query{1} = query_ind{2} /\
        l{1} = lp-1 /\ l{2} = lp /\
          DKCp.b{2} /\
          b{2} /\ DKCp.l{2} = l{2} /\
          DKCp.b{2} = b{2} /\
        EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
        R.t{1}.[lp] = !DKCp.lsb{2} /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> lp => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
        oget R.xx{1}.[(lp, !C.v{1}.[lp])] = DKCp.ksec{2} /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)
      )
      
      ( (={glob A, real, p, DKCp.b, l, b, query_ind} /\
          query_ind{1} = query_ind{2} /\ l{1} = lp /\
          b{2}) /\ 
        EncSecurity.queryValid_IND query_ind{1} /\
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

        ={glob A, real, p, R.t, DKCp.b, l, DKCp.l, DKCp.kpub, b, DKCp.lsb, DKCp.ksec, query_ind} /\
          DKCp.b{2} /\ 
          b{2} /\ i{1} = i1{2} /\ 
          DKCp.b{2} = b{2} /\
        EncSecurity.queryValid_IND query_ind{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        R.t{2}.[lp] = !DKCp.lsb{2} /\ DKCp.used{2} = fset0)
          .

          progress. exists (glob A){2}. exists C.aa{2}. exists C.bb{2}. exists (((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2})). exists (C.gg{2}). exists C.m{2}. exists C.n{2}.  exists C.q{2}. exists C.v{2}. exists (C.x{2}).      exists (DKCp.b{2}). exists (b{2}). exists l{2}. exists (p{2}). exists (query_ind{2}).  exists (real{2}). by progress. by progress.  

      swap{2} 13 -7. swap{2} 14 -5. fusion{2} 14!1 @ 1,4.
      
      wp.
      
  while (={glob A, real, p, i} /\
    query{1} = query_ind{2} /\ ={useVisible} /\ useVisible{2} /\
      0 <= i{1} <= C.n{1} + C.q{1} /\ DKCp.l{2} = lp /\ l{2} = lp /\
    l{1} = lp-1 /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\
      EncSecurity.queryValid_IND query{1} /\ size R.t{1} = C.n{1} + C.q{1} /\
    ={glob C} /\ size R.t{1} = size R.t{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
      size C.v{1} = C.n{1} + C.q{1} /\ 
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
    (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
    (forall (i1 : int),
      C.n{2} <= i1 < C.n{2} + C.q{2} =>
      C.v{2}.[i1] =
      oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
    (forall k, 0 <= k < i{1} => k <> lp => R.t{1}.[k] = R.t{2}.[k]) /\
    (forall k, 0 <= k < i{1} => k = lp => R.t{1}.[k] = !DKCp.lsb{2}) /\
    (forall k, 0 <= k < i{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k <> lp => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k = lp => oget R.xx{1}.[(k,!C.v{1}.[k])] = DKCp.ksec{2}) /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)).
  
    if{2}; last first.

  case ((i < C.n + C.q - C.m){1}).
    swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = lp - 1 /\ l{2} = lp /\ DKCp.l{2} = lp /\
     DKCp.b{2} /\
     b{2} /\
     DKCp.b{2} = b{2} /\
     (EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> lp => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = lp => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> lp =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = lp => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> lp) /\
  i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

   case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

    wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

    case (C.v{1}.[i{1}] = false). wp. swap{2} 2-1. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

     wp. swap{2} 2-1. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

     swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\ DKCp.l{2} = lp /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = lp - 1 /\ l{2} = lp /\
     DKCp.b{2} /\
     b{2} /\
     DKCp.b{2} = b{2} /\
     (EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> lp => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = lp => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> lp =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = lp => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> lp) /\
  ! i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#.

    swap{2} 2-1. wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

    case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

     wp. swap{2} 2-1. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

      wp. rnd{2}. swap{2} 2 2. rnd. rnd. wp. rnd (fun b, !b). 
      auto; progress. by rewrite ?DBool.dboolb. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. by rewrite DBool.dbool_ll.
      
      idtac=>/#.
      idtac=>/#.
      by rewrite size_set.
      by rewrite ?size_set.
      by rewrite size_set.

      by rewrite ?getP ?get_set //= => /#.

      rewrite ?getP get_set //= => /#. 

      rewrite ?getP ?get_set //= => /#. 
  
      by rewrite ?getP ?get_set //= => /#.
      by rewrite ?getP ?get_set //= => /#.

      by rewrite ?getP ?get_set //= => /#.
      by rewrite ?getP ?get_set //= => /#.

        wp. 
      while{2} (={glob A, real, p} /\
   query{1} = query_ind{2} /\ DKCp.l{2} = lp /\
   l{1} = lp - 1 /\ l{2} = lp /\ DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\
  (EncSecurity.queryValid_IND query{1}) /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i1_0 : int), 0 <= i1_0 < C.n{2} => C.v{2}.[i1_0] = C.x{2}.[i1_0]) /\
  (forall (i1_0 : int),
    C.n{2} <= i1_0 < C.n{2} + C.q{2} =>
    C.v{2}.[i1_0] =
    oget C.gg{2}.[(i1_0, C.v{2}.[C.aa{2}.[i1_0]], C.v{2}.[C.bb{2}.[i1_0]])]) /\
  0 <= i{2} <= C.n{2} + C.q{2} /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, false)] = Some W.zeros) /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, true)] = Some W.zeros)
) (C.n{2} + C.q{2} - i{2}).

 auto. progress; expect 5 by rewrite ?getP => /#. 

      wp. skip; progress; first 5  by idtac=>/#.
        by rewrite size_offun max_ler =>/#.
        by rewrite size_offun max_ler =>/#. 
        by idtac=>/#.
        by rewrite ?map0P => /#. by rewrite ?map0P => /#. 
        by rewrite ?map0P. idtac=>/#.  idtac=>/#.
        
        rewrite ?get_set //= => /#.
        idtac=>/#.
        rewrite get_set //= => /#. 
        rewrite get_set //= => /#.  
        rewrite ?getP //= => /#.
        rewrite ?getP //= => /#. 
    rewrite ?getP //= => /#. 
      wp.
      while (={glob A, real, p, R.t, DKCp.b, l, DKCp.l, DKCp.kpub, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ l{1} = lp /\ DKCp.l{2} = lp /\
   i{1} = i1{2} /\ lsb1{2} = DKCp.lsb{2} /\
  i{1} = i1{2} /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
  DKCp.b{2} /\ ={useVisible} /\ useVisible{1} /\
  b{2} /\ size R.t{1} = size R.t{2} /\
  i{1} = i1{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
  DKCp.b{2} = b{2} /\ DKCp.b{1} = b{1} /\
  boundl = SomeGarble.bound /\
  EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
    oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\ DKCp.used{2} = fset0).

        auto; progress; first 2 by idtac=>/#. 
        by rewrite size_set. 

      wp.  
      while (={glob A, real, p, i, DKCp.kpub, DKCp.b, l, DKCp.l, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ l{1} = lp /\ DKCp.l{2} = lp /\
   0 <= i{1} <= C.n{1} + C.q{1} /\
  DKCp.b{2} /\ 
  b{2} /\
  DKCp.b{2} = b{2} /\
  boundl = SomeGarble.bound /\
  EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
     oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\ DKCp.used{2} = fset0).

    if. progress. 
      auto; progress; first 4 by idtac=>/#.
    auto; progress; first 4 by idtac=>/#. 

    wp.
    while (={glob A, real, p, DKCp.b, b, query_ind, i, DKCp.kpub, DKCp.b, DKCp.ksec, DKCp.lsb, b, query_ind} /\
   ={query_ind} /\ 0 <= i{2} <= C.n{2} + C.q{2} /\ l{1} = lp /\ DKCp.l{2} = lp /\
   DKCSecurity.bound = C.n{1} + C.q{1} /\
   DKCp.b{2} /\ b{2} /\ DKCp.b{2} = b{2} /\
  (EncSecurity.queryValid_IND query_ind{1}) /\
  ={glob C} /\
  boundl = SomeGarble.bound /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i1_0 : int), 0 <= i1_0 < C.n{2} => C.v{2}.[i1_0] = C.x{2}.[i1_0]) /\
  (forall (i1_0 : int),
    C.n{2} <= i1_0 < C.n{2} + C.q{2} =>
    C.v{2}.[i1_0] =
    oget C.gg{2}.[(i1_0, C.v{2}.[C.aa{2}.[i1_0]], C.v{2}.[C.bb{2}.[i1_0]])]) /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, false)] = Some W.zeros) /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, true)] = Some W.zeros)
).

  progress. auto; progress; expect 6 by rewrite ?getP => /#. 


    auto; progress; first 10 by idtac=>/#.
      by rewrite size_offun max_ler => /#.
      rewrite get_set //= => /#.  


(******)
(* END OF RANDOM GENERATION *)
(* BEGIN OF GARBLE *)
(******)

    wp. call (_ : true) => //. wp.


(******************************)

while{2} (={glob A, real, p, G.g} /\
    query{1} = query_ind{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    l{1} = lp-1 /\ l{2} = lp /\ DKCp.l{2} = l{2} /\
    0 <= i0{2} <= C.n{2} /\
    DKCp.b{2} /\
    b{2} /\
    DKCp.b{2} = b{2} /\
    EncSecurity.queryValid_IND query{1} /\
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
    R.t{2}.[DKCp.l{2}] = !DKCp.lsb{2} /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} =>
    R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} => k <> DKCp.l{2} =>
    R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
  oget R.xx{1}.[(DKCp.l{2}, ! C.v{1}.[DKCp.l{2}])] = DKCp.ksec{2} /\ ={G.pp} /\ (*/\
    (forall k a b, 0 <= k < G.g{2} => G.pp{1}.[(k, a, b)] = G.pp{2}.[(k,a,b)])*)
  (forall k, C.n{1} <= k < C.n{1} + C.q{1} => mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\
  (forall k, 0 <= k < i0{2} => mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None) /\
  (forall k, 0 <= k < i0{2} => mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, i0{2} <= k < C.n{2} => !mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, 0 <= k < i0{2} => R.xx{2}.[(k, C.v{2}.[k])] = R.xx{1}.[(k, C.v{1}.[k])])
) (C.n{2} - i0{2}).

    progress. inline*. rcondt 5. auto. progress; expect 4 by idtac=>/#. rcondf 10. auto. progress. idtac=>/#. (auto; progress; first 2 by idtac=>/#); first 6 by rewrite ?in_fsetU ?in_fset1 => /#. rewrite in_fsetU in_fset1. cut ->: mem DKCp.used{hr} (tweak k C.x{hr}.[k] R.t{hr}.[0]) <=> false by idtac=>/#. cut ? : k <> i0{hr} by idtac=>/#. by rewrite from_int_inj_fun => /#. by rewrite ?getP => /#. idtac=>/#. 

(******************************)

    wp. inline*.

    while (={glob A, real, p, G.g} /\
    query{1} = query_ind{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    l0{1} = l{1} /\
  l{1} = lp-1 /\ l{2} = lp /\ DKCp.l{2} = l{2} /\ C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
    DKCp.b{2} /\
    b{2} /\ l0{1} = l{1} /\
    DKCp.b{2} = b{2} /\
    EncSecurity.queryValid_IND query{1} /\
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
    R.t{2}.[DKCp.l{2}] = !DKCp.lsb{2} /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} =>
    R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} => k <> DKCp.l{2} =>
    R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
  oget R.xx{1}.[(DKCp.l{2}, ! C.v{1}.[DKCp.l{2}])] = DKCp.ksec{2} /\ ={G.pp} /\ (*/\
    (forall k a b, 0 <= k < G.g{2} => G.pp{1}.[(k, a, b)] = G.pp{2}.[(k,a,b)])*)
  (forall k, C.n{1} <= k < G.g{1} => mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\
  (forall k, G.g{1} <= k < C.n{1} + C.q{1} => !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\
  (forall k, 0 <= k < C.n{1} => !mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)).
  case (! C.aa{2}.[G.g{2}] < DKCp.l{2}).
  rcondt{2} 3. auto.

  rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondf{2} 30. auto; progress => /#. 
    rcondt{2} 40. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. rcondf{2} 45. auto; progress => /#. 
     rcondt{2} 55. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondf{2} 60. auto; progress => /#. 

  auto; progress.
     by rewrite Dword.lossless.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= l{2} - 1 <=> false by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= l{2} - 1 <=> false by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{2} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{2} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{2} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{2} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
     
       rcondf{2} 3. progress. auto.

  case (C.bb{2}.[G.g{2}] = DKCp.l{2}).
  rcondt{2} 3. auto; progress => /#. 

  rcondt{2} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.  rcondt{2} 30. auto; progress => /#. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.  rcondf{2} 46. auto; progress => /#. 
     rcondt{2} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 61. auto; progress => /#. 

  wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
     by rewrite Dword.lossless.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= C.bb{2}.[G.g{2}] - 1 <=> true by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= C.bb{2}.[G.g{2}] - 1 <=> false by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = C.bb{2}.[G.g{2}] && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = C.bb{2}.[G.g{2}] && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
     
    case (! C.bb{2}.[G.g{2}] <= DKCp.l{2}).
    rcondt{2} 3. auto; progress => /#. 
    rcondt{2} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#.  rcondt{2} 30. auto; progress => /#. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. rcondf{2} 46. auto; progress => /#. 
     rcondt{2} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 61. auto; progress => /#. 

  wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
  by rewrite Dword.lossless.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= l{2} - 1 <=> true by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= l{2} - 1 <=> false by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{2} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{2} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{2} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{2} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
     
     rcondf{2} 3. auto; progress => /#. 
     rcondt{2} 10. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 30. auto; progress => /#. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 46. auto; progress => /#. 
     rcondt{2} 57. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 62. auto; progress => /#. 

    auto. progress.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= l{2} - 1 <=> true by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= l{2} - 1 <=> true by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{2} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{2} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{2} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{2} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
     
  auto. progress.
  by idtac=>/#. by idtac=>/#.
  by rewrite size_offun max_ler => /#.
  by idtac=>/#.
  by idtac=>/#.
  by idtac=>/#.
  by idtac=>/#.
  by rewrite in_fset0.
  by rewrite in_fset0.
  by rewrite in_fset0.
  by rewrite in_fset0. by rewrite in_fset0. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. 
       simplify encode; congr; apply fun_ext; rewrite /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < C.n{2}) => hc. simplify. cut ->: mem (dom R.xx{1}) (x, C.x{2}.[x]) by rewrite in_dom => /#. cut ->: mem (dom xx_R) (x, C.x{2}.[x]) by rewrite in_dom => /#. simplify => /#. idtac=>/#. 
  by idtac=>/#.
  rcondf {1} 1. by auto.

  rcondf{2} 16. progress. wp. while ((glob A){m} = (glob A) /\ query{m} = query_ind /\ l{m} = l - 1 /\ DKCp.b /\ b /\ DKCp.b = b /\ ! (EncSecurity.queryValid_IND query{m})). if. auto. auto. auto. while ((glob A){m} = (glob A) /\ query{m} = query_ind /\ l{m} = l - 1 /\ DKCp.b /\ b /\ DKCp.b = b /\ ! (EncSecurity.queryValid_IND query{m})). auto. auto. 
     wp. rnd. wp. while {2} (={glob A} /\ query{1} = query_ind{2} /\ l{1} = lp - 1 /\ l{2} = lp /\ b{2} /\ DKCp.b{2} = b{2} /\ ! (EncSecurity.queryValid_IND query{1})) (DKCSecurity.bound{2} - i{2}). progress. auto. if. auto. progress. smt. smt. smt. idtac=>/#. auto. progress. smt. smt. idtac=>/#.
wp. while {2} (={glob A} /\ query{1} = query_ind{2} /\ l{1} = lp - 1 /\ l{2} = lp /\ b{2} /\ DKCp.b{2} = b{2} /\ ! (EncSecurity.queryValid_IND query{1})) (DKCSecurity.bound{2} - i{2}). auto. progress. idtac=>/#. auto.
 progress. idtac=>/#. idtac=>/#. idtac=>/#.
qed.

lemma GameHybrid_l_sim (A <: EncSecurity.Adv_IND_t{DKC_Adv,DKCp,DKC}) lp:
  islossless A.gen_query =>
  islossless A.get_challenge =>
  0 <= lp < boundl =>
  equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game:
    ={glob A} /\ l{1} = lp /\ l{2} = lp /\ !b{2} ==> res{1} <> res{2}].
proof.
 move => Agen_ll Aget_ll hl.
  proc => //.
  inline DKC.initialize DKC_Adv(DKC, A).get_challenge.
  swap{2} 16 -15.
  seq 1 1 : (={glob A} /\ l{1} = lp /\ l{2} = lp /\ !b{2} /\ query{1} = query_ind{2}); first by call (_ : true).

  case (EncSecurity.queryValid_IND query{1}).
    rcondt{1} 1; first by progress.
    rcondt{2} 16. auto. while (true). auto. wp. while (true). auto. by auto. 
    swap{2} 16 -15.
    swap{2} 17 -15.
    swap{2} 18 -15.
    seq 3 3 : ((={glob A,real,p} /\
      query{1} = query_ind{2} /\ 
      l{1} = lp /\ l{2} = lp /\ !b{2}) /\
      EncSecurity.queryValid_IND query{1} /\ ={glob C} /\
      size C.v{1} = (C.n + C.q){1} /\
      C.f{1} = ((C.n, C.m, C.q, C.aa, C.bb), C.gg){1} /\
      validInputsP (C.f, C.x){1} /\
      (forall i, 0 <= i < C.n{2} => C.v{2}.[i] = C.x{2}.[i]) /\
      (forall i, C.n <= i < C.n + C.q => C.v{2}.[i] = oget C.gg.[(i, C.v{2}.[C.aa{2}.[i]], C.v{2}.[C.bb.[i]])]){2}).
      call CircuitInitEquiv'.
      auto; progress. 
        by move : H0; rewrite /queryValid_IND /valid_plain /validInputs /validInputsP ?valid_wireinput /valid_circuitP /fst /snd; case realL. 
        (*by simplify validBound; case realL => /#.*)

    seq 1 16 : (={glob A, real, p} /\
      query{1} = query_ind{2} /\
      l{1} = lp /\ l{2} = lp /\ DKCp.l{2} = l{2} /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\
      EncSecurity.queryValid_IND query{1} /\ 
      ={glob C} /\ 
      size C.v{1} = C.n{1} + C.q{1} /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
      (forall (i0 : int), 0 <= i0 < C.n{2} => C.v{2}.[i0] = C.x{2}.[i0]) /\
      (forall (i0 : int),
        C.n{2} <= i0 < C.n{2} + C.q{2} =>
        C.v{2}.[i0] =
        oget C.gg{2}.[(i0, C.v{2}.[C.aa{2}.[i0]], C.v{2}.[C.bb{2}.[i0]])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
      R.t{2}.[lp] = !DKCp.lsb{2} /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> lp => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
        oget R.xx{1}.[(lp, !C.v{1}.[lp])] = DKCp.ksec{2} /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)).
    
      inline RandomInit.init AdvInit(DKC).init.

      transitivity{2} {
        b0 = b;
        l0 = l;
    
        DKCp.lsb = witness;
        DKCp.ksec = witness;
        DKCp.b = b0;
        DKCp.l = l0;
        DKCp.used = fset0;
        DKCp.kpub = map0;
      
        i = 0;

        while (i < C.n + C.q) {
          DKCp.kpub.[(i, false)] = W.zeros;
          DKCp.kpub.[(i, true)] = W.zeros;
          i = i + 1;
        }
      
        i = 0;
        while (i < C.n + C.q) {
          if (i = lp) {
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
        R.t.[DKCp.l] = !DKCp.lsb;
      }
      ( (={glob A, real, p} /\
          query{1} = query_ind{2} /\
          l{1} = lp /\ !b{2} /\ l{2} = lp) /\
        EncSecurity.queryValid_IND query{1} /\
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

        ={glob A, real, p} /\
        query{1} = query_ind{2} /\
        l{1} = lp /\ l{2} = lp /\
          !DKCp.b{2} /\
          !b{2} /\ DKCp.l{2} = l{2} /\
          DKCp.b{2} = b{2} /\
        EncSecurity.queryValid_IND query{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.t{1}.[k] = R.t{2}.[k]) /\
        R.t{1}.[lp] = !DKCp.lsb{2} /\
        (forall k, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => k <> lp => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
        oget R.xx{1}.[(lp, !C.v{1}.[lp])] = DKCp.ksec{2} /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)
      )
      
      ( (={glob A, real, p, DKCp.b, l, b, query_ind} /\
          query_ind{1} = query_ind{2} /\ l{1} = lp /\
          !b{2}) /\ 
        EncSecurity.queryValid_IND query_ind{1} /\
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

        ={glob A, real, p, R.t, DKCp.b, l, DKCp.l, DKCp.kpub, b, DKCp.lsb, DKCp.ksec, query_ind} /\
          !DKCp.b{2} /\ 
          !b{2} /\ i{1} = i1{2} /\ 
          DKCp.b{2} = b{2} /\
        EncSecurity.queryValid_IND query_ind{1} /\
        ={glob C} /\
          size C.v{1} = C.n{1} + C.q{1} /\
          C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
          validInputsP (C.f{1}, C.x{1}) /\
        (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
        (forall (i0_0 : int),
          C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
          C.v{2}.[i0_0] =
          oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\
        R.t{2}.[lp] = !DKCp.lsb{2} /\ DKCp.used{2} = fset0)
          .

          progress. exists (glob A){2}. exists C.aa{2}. exists C.bb{2}. exists (((C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}), C.gg{2})). exists (C.gg{2}). exists C.m{2}. exists C.n{2}.  exists C.q{2}. exists C.v{2}. exists (C.x{2}).      exists (DKCp.b{2}). exists (b{2}). exists l{1}. exists (p{2}). exists (query_ind{2}).  exists (real{2}). by progress. by progress.  

      swap{2} 13 -7. swap{2} 14 -5. fusion{2} 14!1 @ 1,4.
      
      wp.
      
  while (={glob A, real, p, i} /\
    query{1} = query_ind{2} /\ ={useVisible} /\ useVisible{2} /\
      0 <= i{1} <= C.n{1} + C.q{1} /\ DKCp.l{2} = lp /\ l{2} = lp /\
    l{1} = lp /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\
      EncSecurity.queryValid_IND query{1} /\ size R.t{1} = C.n{1} + C.q{1} /\
    ={glob C} /\ size R.t{1} = size R.t{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
      size C.v{1} = C.n{1} + C.q{1} /\ 
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
      validInputsP (C.f{1}, C.x{1}) /\
    (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
    (forall (i1 : int),
      C.n{2} <= i1 < C.n{2} + C.q{2} =>
      C.v{2}.[i1] =
      oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
    (forall k, 0 <= k < i{1} => k <> lp => R.t{1}.[k] = R.t{2}.[k]) /\
    (forall k, 0 <= k < i{1} => k = lp => R.t{1}.[k] = !DKCp.lsb{2}) /\
    (forall k, 0 <= k < i{1} => R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k <> lp => R.xx{1}.[(k, !C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{1}.[k])]) /\
    (forall k, 0 <= k < i{1} => k = lp => oget R.xx{1}.[(k,!C.v{1}.[k])] = DKCp.ksec{2}) /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)).
  
    if{2}; last first.

  case ((i < C.n + C.q - C.m){1}).
    swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = lp /\ l{2} = lp /\ DKCp.l{2} = lp /\
     !DKCp.b{2} /\
     !b{2} /\
     DKCp.b{2} = b{2} /\
     (EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> lp => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = lp => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> lp =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = lp => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> lp) /\
  i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

   case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

    wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

    case (C.v{1}.[i{1}] = false). wp. swap{2} 2-1. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

     wp. swap{2} 2-1. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

     swap{2} 5 -4.
      seq 1 1 : ((((={glob A, real, p, i} /\
     query{1} = query_ind{2} /\
     ={useVisible} /\
     useVisible{2} /\ DKCp.l{2} = lp /\
     0 <= i{1} <= C.n{1} + C.q{1} /\
     l{1} = lp /\ l{2} = lp /\
     !DKCp.b{2} /\
     !b{2} /\
     DKCp.b{2} = b{2} /\
     (EncSecurity.queryValid_IND query{1}) /\
     size R.t{1} = C.n{1} + C.q{1} /\
     ={glob C} /\
     size R.t{1} = size R.t{2} /\
     size R.t{1} = C.n{1} + C.q{1} /\
     size C.v{1} = C.n{1} + C.q{1} /\
     C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
     validInputsP (C.f{1}, C.x{1}) /\
     (forall (i1 : int), 0 <= i1 < C.n{2} => C.v{2}.[i1] = C.x{2}.[i1]) /\
     (forall (i1 : int),
        C.n{2} <= i1 < C.n{2} + C.q{2} =>
        C.v{2}.[i1] =
        oget C.gg{2}.[(i1, C.v{2}.[C.aa{2}.[i1]], C.v{2}.[C.bb{2}.[i1]])]) /\
     (forall (k : int),
        0 <= k < i{1} => k <> lp => R.t{1}.[k] = R.t{2}.[k]) /\
     (forall (k : int),
        0 <= k < i{1} => k = lp => R.t{1}.[k] = !DKCp.lsb{2}) /\
     (forall (k : int),
        0 <= k < i{1} =>
        R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{1}.[k])]) /\
     (forall (k : int),
        0 <= k < i{1} =>
        k <> lp =>
        R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, ! R.t{1}.[k])]) /\
     (forall (k : int),
       0 <= k < i{1} =>
     k = lp => oget R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.ksec{2}) /\ DKCp.used{2} = fset0 /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
      (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None) /\
    i{1} < C.n{1} + C.q{1} /\ i{2} < C.n{2} + C.q{2}) /\
   i{2} <> lp) /\
  ! i{1} < C.n{1} + C.q{1} - C.m{1} /\ ={trnd})). by auto. 

case (trnd{1} = false). case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#.

    swap{2} 2-1. wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

    case (C.v{1}.[i{1}] = false). wp. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

     wp. swap{2} 2-1. rnd. rnd. wp. ((auto; progress; first 6 by idtac=>/#); first 3 by rewrite ?size_set); first 7 by rewrite ?getP H ?get_set //= => /#. 

      wp. rnd{2}. swap{2} 2 2. rnd. rnd. wp. rnd (fun b, !b). 
      auto; progress. by rewrite ?DBool.dboolb. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. by rewrite DBool.dbool_ll.
      
      idtac=>/#.
      idtac=>/#.
      by rewrite size_set.
      by rewrite ?size_set.
      by rewrite size_set.

      by rewrite ?getP ?get_set //= => /#.

      rewrite ?getP get_set //= => /#. 

      rewrite ?getP ?get_set //= => /#. 
  
      by rewrite ?getP ?get_set //= => /#.
      by rewrite ?getP ?get_set //= => /#.

      by rewrite ?getP ?get_set //= => /#.
      by rewrite ?getP ?get_set //= => /#.

        wp. 
      while{2} (={glob A, real, p} /\
   query{1} = query_ind{2} /\ DKCp.l{2} = lp /\
   l{1} = lp /\ l{2} = lp /\ !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\
  (EncSecurity.queryValid_IND query{1}) /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i1_0 : int), 0 <= i1_0 < C.n{2} => C.v{2}.[i1_0] = C.x{2}.[i1_0]) /\
  (forall (i1_0 : int),
    C.n{2} <= i1_0 < C.n{2} + C.q{2} =>
    C.v{2}.[i1_0] =
    oget C.gg{2}.[(i1_0, C.v{2}.[C.aa{2}.[i1_0]], C.v{2}.[C.bb{2}.[i1_0]])]) /\
  0 <= i{2} <= C.n{2} + C.q{2} /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, false)] = Some W.zeros) /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, true)] = Some W.zeros)
) (C.n{2} + C.q{2} - i{2}).

 auto. progress; expect 5 by rewrite ?getP => /#. 

      wp. skip; progress; first 5  by idtac=>/#.
        by rewrite size_offun max_ler =>/#.
        by rewrite size_offun max_ler =>/#. 
        by idtac=>/#.
        by rewrite ?map0P => /#. by rewrite ?map0P => /#. 
        by rewrite ?map0P. idtac=>/#.  idtac=>/#.
        
        rewrite ?get_set //= => /#.
        idtac=>/#.
        rewrite get_set //= => /#. 
        rewrite get_set //= => /#.  
        rewrite ?getP //= => /#.
        rewrite ?getP //= => /#. 
    rewrite ?getP //= => /#. 
      wp.
      while (={glob A, real, p, R.t, DKCp.b, l, DKCp.l, DKCp.kpub, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ l{1} = lp /\ DKCp.l{2} = lp /\
   i{1} = i1{2} /\ lsb1{2} = DKCp.lsb{2} /\
  i{1} = i1{2} /\ 0 <= i{1} <= C.n{1} + C.q{1} /\
  !DKCp.b{2} /\ ={useVisible} /\ useVisible{1} /\
  !b{2} /\ size R.t{1} = size R.t{2} /\
  i{1} = i1{2} /\ size R.t{1} = C.n{1} + C.q{1} /\
  DKCp.b{2} = b{2} /\ DKCp.b{1} = b{1} /\
  boundl = SomeGarble.bound /\
  EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
    oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\ DKCp.used{2} = fset0).

        auto; progress; first 2 by idtac=>/#. 
        by rewrite size_set. 

      wp.  
      while (={glob A, real, p, i, DKCp.kpub, DKCp.b, l, DKCp.l, DKCp.ksec, DKCp.lsb, b, query_ind} /\
      DKCSecurity.bound = C.n{1} + C.q{1} /\ l{1} = lp /\ DKCp.l{2} = lp /\
   0 <= i{1} <= C.n{1} + C.q{1} /\
  !DKCp.b{2} /\ 
  !b{2} /\
  DKCp.b{2} = b{2} /\
  boundl = SomeGarble.bound /\
  EncSecurity.queryValid_IND query_ind{1} /\
  ={glob C} /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i0_0 : int), 0 <= i0_0 < C.n{2} => C.v{2}.[i0_0] = C.x{2}.[i0_0]) /\
  (forall (i0_0 : int),
     C.n{2} <= i0_0 < C.n{2} + C.q{2} =>
     C.v{2}.[i0_0] =
     oget C.gg{2}.[(i0_0, C.v{2}.[C.aa{2}.[i0_0]], C.v{2}.[C.bb{2}.[i0_0]])]) /\ DKCp.used{2} = fset0).

    if. progress. 
      auto; progress; first 4 by idtac=>/#.
    auto; progress; first 4 by idtac=>/#. 

    wp.
    while (={glob A, real, p, DKCp.b, b, query_ind, i, DKCp.kpub, DKCp.b, DKCp.ksec, DKCp.lsb, b, query_ind} /\
   ={query_ind} /\ 0 <= i{2} <= C.n{2} + C.q{2} /\ l{1} = lp /\ DKCp.l{2} = lp /\
   DKCSecurity.bound = C.n{1} + C.q{1} /\
   !DKCp.b{2} /\ !b{2} /\ DKCp.b{2} = b{2} /\
  (EncSecurity.queryValid_IND query_ind{1}) /\
  ={glob C} /\
  boundl = SomeGarble.bound /\
  size C.v{1} = C.n{1} + C.q{1} /\
  C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\
  validInputsP (C.f{1}, C.x{1}) /\
  (forall (i1_0 : int), 0 <= i1_0 < C.n{2} => C.v{2}.[i1_0] = C.x{2}.[i1_0]) /\
  (forall (i1_0 : int),
    C.n{2} <= i1_0 < C.n{2} + C.q{2} =>
    C.v{2}.[i1_0] =
    oget C.gg{2}.[(i1_0, C.v{2}.[C.aa{2}.[i1_0]], C.v{2}.[C.bb{2}.[i1_0]])]) /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, false)] = Some W.zeros) /\
  (forall k, 0 <= k < i{2} => DKCp.kpub{2}.[(k, true)] = Some W.zeros)
).

  progress. auto; progress; expect 6 by rewrite ?getP => /#. 


    auto; progress; first 10 by idtac=>/#.
      by rewrite size_offun max_ler => /#.
      rewrite get_set //= => /#.  

 
(******)
(* END OF RANDOM GENERATION *)
(* BEGIN OF GARBLE *)
(******)

    wp. call (_ : true) => //. wp.


(******************************)

while{2} (={glob A, real, p, G.g} /\
    query{1} = query_ind{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    l{1} = lp /\ l{2} = lp /\ DKCp.l{2} = l{2} /\
    0 <= i0{2} <= C.n{2} /\
    !DKCp.b{2} /\
    !b{2} /\
    DKCp.b{2} = b{2} /\
    EncSecurity.queryValid_IND query{1} /\
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
    R.t{2}.[DKCp.l{2}] = !DKCp.lsb{2} /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} =>
    R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} => k <> DKCp.l{2} =>
    R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
  oget R.xx{1}.[(DKCp.l{2}, ! C.v{1}.[DKCp.l{2}])] = DKCp.ksec{2} /\ ={G.pp} /\ (*/\
    (forall k a b, 0 <= k < G.g{2} => G.pp{1}.[(k, a, b)] = G.pp{2}.[(k,a,b)])*)
  (forall k, C.n{1} <= k < C.n{1} + C.q{1} => mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\
  (forall k, 0 <= k < i0{2} => mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None) /\
  (forall k, 0 <= k < i0{2} => mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, i0{2} <= k < C.n{2} => !mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, 0 <= k < i0{2} => R.xx{2}.[(k, C.v{2}.[k])] = R.xx{1}.[(k, C.v{1}.[k])])
) (C.n{2} - i0{2}).

    progress. inline*. rcondt 5. auto. progress; expect 4 by idtac=>/#. rcondf 10. auto. progress. idtac=>/#. (auto; progress; first 2 by idtac=>/#); first 6 by rewrite ?in_fsetU ?in_fset1 => /#. rewrite in_fsetU in_fset1. cut ->: mem DKCp.used{hr} (tweak k C.x{hr}.[k] R.t{hr}.[0]) <=> false by idtac=>/#. cut ? : k <> i0{hr} by idtac=>/#. by rewrite from_int_inj_fun => /#. by rewrite ?getP => /#. idtac=>/#. 

(******************************)

    wp. inline*.

    while (={glob A, real, p, G.g} /\
    query{1} = query_ind{2} /\
    DKCSecurity.bound = C.n{1} + C.q{1} /\
    l0{1} = l{1} /\
  l{1} = lp /\ l{2} = lp /\ DKCp.l{2} = l{2} /\ C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
    !DKCp.b{2} /\
    !b{2} /\ l0{1} = l{1} /\
    DKCp.b{2} = b{2} /\
    EncSecurity.queryValid_IND query{1} /\
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
    R.t{2}.[DKCp.l{2}] = !DKCp.lsb{2} /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} =>
    R.xx{1}.[(k, C.v{1}.[k])] = DKCp.kpub{2}.[(k, R.t{2}.[k])]) /\
  (forall (k : int),
    0 <= k < C.n{1} + C.q{1} => k <> DKCp.l{2} =>
    R.xx{1}.[(k, ! C.v{1}.[k])] = DKCp.kpub{2}.[(k, !R.t{2}.[k])]) /\
  oget R.xx{1}.[(DKCp.l{2}, ! C.v{1}.[DKCp.l{2}])] = DKCp.ksec{2} /\ ={G.pp} /\ (*/\
    (forall k a b, 0 <= k < G.g{2} => G.pp{1}.[(k, a, b)] = G.pp{2}.[(k,a,b)])*)
  (forall k, C.n{1} <= k < G.g{1} => mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\
  (forall k, G.g{1} <= k < C.n{1} + C.q{1} => !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ false)) /\ !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ false) (R.t{2}.[C.bb{1}.[k]] ^^ true)) /\ !mem DKCp.used{2} (tweak k (R.t{2}.[C.aa{1}.[k]] ^^ true) (R.t{2}.[C.bb{1}.[k]] ^^ true))) /\
  (forall k, 0 <= k < C.n{1} => !mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0])) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, R.t{2}.[k])] <> None) /\
  (forall k, 0 <= k < C.n{1} + C.q{1} => DKCp.kpub{2}.[(k, !R.t{2}.[k])] <> None)).

case (!C.aa{2}.[G.g{2}] <= DKCp.l{2}).
  rcondt{2} 3. auto. progress => /#.

  rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondf{2} 30. auto; progress => /#. 
    rcondt{2} 40. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. rcondf{2} 45. auto; progress. cut ->: l{m} = C.aa{hr}.[G.g{hr}] <=> false by idtac=> /#. cut ->: l{m} = C.bb{hr}.[G.g{hr}] <=> false by idtac=>/#. by simplify.
     rcondt{2} 55. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondf{2} 60. auto; progress. cut ->: l{m} = C.aa{hr}.[G.g{hr}] <=> false by idtac=> /#. cut ->: l{m} = C.bb{hr}.[G.g{hr}] <=> false by idtac=>/#. by simplify. 

  auto; progress.
     by rewrite Dword.lossless.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= l{1} <=> false by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= l{1} <=> false by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{1} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{1} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{1} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{1} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
     
  case (C.aa{2}.[G.g{2}] = DKCp.l{2}).
  rcondt{2} 3. auto.   

  rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 30. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. rcondf{2} 46. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 
     rcondt{2} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 61. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 

  wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
     by rewrite Dword.lossless.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     (*cut ->: C.aa{2}.[G.g{2}] <= C.aa{2}.[G.g{2}] <=> true by idtac=>/#.*)
     cut ->: C.bb{2}.[G.g{2}] <= C.aa{2}.[G.g{2}] <=> false by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = C.aa{2}.[G.g{2}] && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = C.aa{2}.[G.g{2}] && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

  rcondf{2} 3. progress. auto. progress => /#. 

  case (C.bb{2}.[G.g{2}] = DKCp.l{2}).
  rcondt{2} 3. auto; progress => /#. 

  rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 30. auto; progress. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. rcondt{2} 46. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. 
     rcondt{2} 57. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 62. auto; progress.  

       auto; progress.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= C.bb{2}.[G.g{2}] <=> true by idtac=>/#.
     (*cut ->: C.bb{2}.[G.g{2}] <= C.bb{2}.[G.g{2}] <=> true by move : H9; simplify validInputsP valid_circuitP fst snd => /#.*)
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = C.bb{2}.[G.g{2}] && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = C.bb{2}.[G.g{2}] && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

   
  case (! C.bb{2}.[G.g{2}] <= DKCp.l{2}).

     rcondt{2} 3. auto. progress. idtac=>/#. idtac=>/#. 
     rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress. 
    rcondt{2} 41. progress. auto. progress.  rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=> /#. rcondf{2} 46. auto; progress. by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     rcondt{2} 56. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. rcondt{2} 61. auto; progress.  

    wp. rnd. wp. rnd{1}. wp. rnd. wp. auto; progress.
     by rewrite Dword.lossless.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= l{1} <=> true by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= l{1} <=> false by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{1} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{1} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{1} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{1} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 
     
rcondf{2} 3. auto. progress => /#. 
rcondt{2} 10. progress. auto. progress. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondf{2} 15. auto. progress. idtac=>/#.  
    rcondt{2} 25. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. done. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 30. auto; progress. 
    rcondt{2} 41. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 46. auto; progress. 
     rcondt{2} 57. progress. auto. progress. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{hr}
     (tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
        (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true)) <=> false by idtac=>/#. cut ->: tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ true)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ true) =
   tweak G.g{hr} (R.t{hr}.[C.aa{hr}.[G.g{hr}]] ^^ false)
     (R.t{hr}.[C.bb{hr}.[G.g{hr}]] ^^ false) <=> false. by rewrite from_int_inj_fun => /#. rewrite ?xor_true ?xor_false. case (R.t{hr}.[C.aa{hr}.[G.g{hr}]]); case (R.t{hr}.[C.bb{hr}.[G.g{hr}]]); rewrite from_int_inj_fun; simplify bti. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. idtac=>/#. rewrite from_int_inj_fun => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rcondt{2} 62. auto. progress. 


     auto; progress.
     by idtac=>/#.
     by idtac=>/#. 
     by rewrite ?size_set.
     by rewrite ?size_set.
     cut ->: C.aa{2}.[G.g{2}] <= l{1} <=> true by idtac=>/#.
     cut ->: C.bb{2}.[G.g{2}] <= l{1} <=> true by move : H9; simplify validInputsP valid_circuitP fst snd => /#.
     
       rewrite ?xor_true ?xor_false //=. congr. congr. congr. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by rewrite ?H12; first 2 by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{1} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{1} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. case (C.aa{2}.[G.g{2}] = l{1} && R.t{2}.[C.aa{2}.[G.g{2}]] = DKCp.lsb{2}) => hc. idtac=>/#. case(C.bb{2}.[G.g{2}] = l{1} && R.t{2}.[C.bb{2}.[G.g{2}]] = DKCp.lsb{2}) => hc'. idtac=>/#. by rewrite H14; first by move : H9; simplify validInputsP valid_circuitP fst snd => /#. idtac=>/#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. congr. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. by move : H9; simplify validInputsP valid_circuitP fst snd => /#. rewrite ?in_fsetU. left. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. idtac=>/#. rewrite ?in_fsetU. left. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. idtac=>/#. rewrite ?in_fsetU. left. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. idtac=>/#. rewrite ?in_fsetU. case (k = G.g{2}) => hk. right. rewrite in_fset1. rewrite hk. done. left. left. left. left. idtac=>/#. cut ? : k <> G.g{2} by idtac=>/#. rewrite ?in_fsetU ?in_fset1. cut ->: mem DKCp.used{2}
        (tweak k (R.t{2}.[C.aa{2}.[k]] ^^ false)
           (R.t{2}.[C.bb{2}.[k]] ^^ false)) <=> false by idtac=>/#. rewrite ?xor_true ?xor_false. cut ->: tweak k (R.t{2}.[C.aa{2}.[k]]) (R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} (R.t{2}.[C.aa{2}.[G.g{2}]])
        (R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] R.t{2}.[C.bb{2}.[k]] =
          tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#.

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]]) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) R.t{2}.[C.bb{2}.[k]] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k R.t{2}.[C.aa{2}.[k]] (!R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k R.t{2}.[C.aa{2}.[k]] (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2}
        (tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]])) <=> false by idtac=>/#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k (! R.t{2}.[C.aa{2}.[k]]) (! R.t{2}.[C.bb{2}.[k]]) =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 

        rewrite ?in_fsetU ?in_fset1. rewrite ?xor_true ?xor_false. cut ->: mem DKCp.used{2} (tweak k C.x{2}.[k] R.t{2}.[0]) <=> false by idtac=>/#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
      tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
     tweak G.g{2} (! R.t{2}.[C.aa{2}.[G.g{2}]]) R.t{2}.[C.bb{2}.[G.g{2}]] <=> false by rewrite from_int_inj_fun => /#. cut ->: tweak k C.x{2}.[k] R.t{2}.[0] =
    tweak G.g{2} R.t{2}.[C.aa{2}.[G.g{2}]] (! R.t{2}.[C.bb{2}.[G.g{2}]]) <=> false by rewrite from_int_inj_fun => /#. by rewrite from_int_inj_fun => /#. 



  auto. progress.
  by idtac=>/#. by idtac=>/#.
  by rewrite size_offun max_ler => /#.
  by idtac=>/#.
  by idtac=>/#.
  by idtac=>/#.
  by idtac=>/#.
  by rewrite in_fset0.
  by rewrite in_fset0.
  by rewrite in_fset0.
  by rewrite in_fset0. by rewrite in_fset0. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. idtac=>/#. 
       simplify encode; congr; apply fun_ext; rewrite /(==) => x. congr. simplify inputK fst snd. rewrite ?filterP. simplify. case (0 <= x < C.n{2}) => hc. simplify. cut ->: mem (dom R.xx{1}) (x, C.x{2}.[x]) by rewrite in_dom => /#. cut ->: mem (dom xx_R) (x, C.x{2}.[x]) by rewrite in_dom => /#. simplify => /#. idtac=>/#. 
  by idtac=>/#.
  rcondf {1} 1. by auto.

  rcondf{2} 16. progress. wp. while ((glob A){m} = (glob A) /\ query{m} = query_ind /\ l{m} = l /\ !DKCp.b /\ !b /\ DKCp.b = b /\ ! (EncSecurity.queryValid_IND query{m})). if. auto. auto. auto. while ((glob A){m} = (glob A) /\ query{m} = query_ind /\ l{m} = l /\ !DKCp.b /\ !b /\ DKCp.b = b /\ ! (EncSecurity.queryValid_IND query{m})). auto. auto. 
     wp. rnd. wp. while {2} true (DKCSecurity.bound{2} - i{2}). auto. if. auto. progress. smt. smt. smt. idtac=>/#. auto. progress. smt. smt. idtac=>/#. wp. while {2} true (DKCSecurity.bound{2} - i{2}). auto. progress. idtac=>/#. auto.
 progress. idtac=>/#. idtac=>/#. idtac=>/#.
qed.

    (*************)
    (* REDUCTION *)
    (*************)

    require import OldMonoid.
    require import Sum.


lemma reductionSimplified (A <: EncSecurity.Adv_IND_t{Rand,R,C,DKC_Adv,DKCp,DKC}) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
  Pr[GameHybrid(A).garble(-1) @ &m : res] - Pr[GameHybrid(A).garble(bound-1) @ &m : res] =
  Mrplus.sum (fun i, (Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game(true,i)@ &m:res] - Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game(false,i)@ &m:!res])) (intval 0 (bound-1)).
proof.
move => Agen_ll Aget_ll.

(* FIRST CUT *)
  cut ->: Pr[GameHybrid(A).garble(-1) @ &m : res] - Pr[GameHybrid(A).garble(SomeGarble.bound - 1) @ &m : res] = Pr[GameHybrid(A).garble(-1) @ &m : res] - Pr[GameHybrid(A).garble(SomeGarble.bound - 1) @ &m : res] + Mrplus.sum (fun i, Pr[GameHybrid(A).garble(i) @ &m : res] - Pr[GameHybrid(A).garble(i) @ &m : res]) (intval 0 (bound-2)). simplify. rewrite (Mrplus.NatMul.sum_const (0%r) (fun (_ : int) => 0%r) (intval 0 (SomeGarble.bound - 2))). done. rewrite intval_card_0. smt. simplify. cut ->: Mrplus.NatMul.( * ) (SomeGarble.bound - 2 + 1) 0%r = 0%r. idtac=>/#. done.
(* /FIRST CUT *)

(* SECOND CUT *)
cut ->: Pr[GameHybrid(A).garble(-1) @ &m : res] - Pr[GameHybrid(A).garble(SomeGarble.bound - 1) @ &m : res] + (Mrplus.sum
   (fun (i : int) =>
      Pr[GameHybrid(A).garble(i) @ &m : res] -
      Pr[GameHybrid(A).garble(i) @ &m : res])
    (intval 0 (SomeGarble.bound - 2))) = Mrplus.sum (fun i, Pr[GameHybrid(A).garble(i-1) @ &m : res] - Pr[GameHybrid(A).garble(i) @ &m : res]) (intval 0 (bound-1)). simplify. rewrite (Mrplus.NatMul.sum_const (0%r) _ (intval 0 (SomeGarble.bound - 2))). progress. cut ->: Mrplus.NatMul.( * ) (card (intval 0 (SomeGarble.bound - 2))) (0%r) = 0%r. smt. simplify.

      rewrite -(intind (fun x, (Pr[GameHybrid(A).garble(-1) @ &m : res] -
Pr[GameHybrid(A).garble(x - 1) @ &m : res] =
(Mrplus.sum
   (fun (i : int) =>
      Pr[GameHybrid(A).garble(i - 1) @ &m : res] -
      Pr[GameHybrid(A).garble(i) @ &m : res])
   (intval 0 (x - 1)))))). progress. simplify intval. rewrite List.Iota.iota0. trivial. rewrite -set0E. rewrite Mrplus.sum_empty. done. progress. rewrite (Mrplus.sum_rm (fun (i0 : int) =>
      Pr[GameHybrid(A).garble(i0 - 1) @ &m : res] -
      Pr[GameHybrid(A).garble(i0) @ &m : res]) (intval 0 (i + 1 - 1)) (i + 1 - 1)). smt. simplify. cut ->: i + 1 - 1 = i by idtac=>/#. cut ->: intval 0 i `\` fset1 i = intval 0 (i-1). rewrite fsetP => x. rewrite in_fsetD ?intval_def. smt. rewrite -H0. smt. smt. done.
(* /SECOND CUT *)

  (* THIRD CUT *)
     cut ->: Mrplus.sum
   (fun (i : int) =>
      Pr[GameHybrid(A).garble(i - 1) @ &m : res] -
      Pr[GameHybrid(A).garble(i) @ &m : res])
   (intval 0 (SomeGarble.bound - 1)) = Mrplus.sum (fun (i : int) =>
      Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game(true,i) @ &m : res] -
      Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game(false,i) @ &m : !res]) (intval 0 (SomeGarble.bound - 1)).

    rewrite (Mrplus.sum_eq (fun (i : int) =>
      Pr[GameHybrid(A).garble(i - 1) @ &m : res] -
      Pr[GameHybrid(A).garble(i) @ &m : res]) (fun (i : int) => 
      Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game(true,i) @ &m : res] -
      Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).game(false,i) @ &m : !res]) (intval 0 (SomeGarble.bound - 1))).

        move => x. rewrite intval_def. progress. congr. byequiv (GameHybrid_l1_sim (A) (x) Agen_ll Aget_ll _). idtac=>/#. done. done. congr. byequiv (GameHybrid_l_sim (A) (x) Agen_ll Aget_ll _). idtac=>/#. done. smt. done. done.
  qed.

(*lemma sch_is_ind (A <: EncSecurity.Adv_IND_t{Rand,R,R',G,C,DKCp,DKC,AdvInit,DKC_Adv}) &m lp:
  islossless A.gen_query =>
  islossless A.get_challenge =>
  0 <= lp < boundl =>  
  `|2%r * Pr[EncSecurity.Game_IND(Rand,A).main()@ &m:res] - 1%r| =
    2%r * (bound)%r * `|2%r * Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, A)).main(lp)@ &m:res] - 1%r|.
proof. 
  move => AgenL AgetL hl.
  rewrite -(GameHybrid0_Game_IND_pr A &m) // -{1}(GameHybridBound_pr A &m) //=.
  cut -> : forall a b, 2%r * a - 2%r * b = 2%r * (a - b) by idtac=>/#. 
  rewrite (reductionSimplified A &m lp). apply AgenL. apply AgetL. apply hl.
  cut H: forall (a b:real), 0%r <= a => `| a * b | = a * `| b | by idtac=>/#.
  rewrite !H=> //; first by smt. 
  by idtac=>/#.
qed.

lemma sch_is_sim (A <: EncSecurity.Adv_SIM_t {Rand, DKCp, C, G, R',DKC,AdvInit,DKC_Adv}) &m lp:
 islossless A.gen_query =>
 islossless A.get_challenge =>
 0 <= lp < boundl =>  
  `|2%r * Pr[EncSecurity.Game_SIM(Rand,EncSecurity.SIM(Rand),A).main()@ &m:res] - 1%r| <=
    2%r * (bound)%r * `|2%r * Pr[DKCSecurity.Game(DKC, DKC_Adv(DKC, EncSecurity.RedSI(A))).main(lp)@ &m:res] - 1%r|.
proof.
  move=> ll_ADVp1 ll_ADVp2 hl.
  rewrite -(sch_is_ind (EncSecurity.RedSI(A)) &m lp _ _).
    by apply (EncSecurity.RedSIgenL A).
    by apply (EncSecurity.RedSIgetL A).
    by apply hl.
  apply (EncSecurity.ind_implies_sim Rand A _ _ &m _)=> //.
  by apply sch_is_pi.
qed.*)

end SomeGarble.
export SomeGarble.
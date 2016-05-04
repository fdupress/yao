(** Definitions of a concrete Garble scheme *)

require import Real.
require import Int.
require import FSet.
require import FMap.
require import Array.
require import Distr.
require import Bool.
require import Pair.

require (*--*) DKC.
require (*--*) DKCSec.
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
  clone import DKCSec.DKCSecurity with theory WD <- W.

  (** Tweak theory, instantiated with the words defined in W *)
  clone import Tweak with theory WT <- W.

  (** Auxiliar types used in the definition of the scheme *)
  (** Tokens type **)
  (** 
    Type of the tokens ((X_0^0, X_0^1), ..., (X_n^0, X_n^1)) that represent the randomness used in the garble scheme.

    The tokens are represented as a map, i.e., X_i^b = X.[i,b].
  *)
  type tokens_t = (int * bool, word) map.

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
  type 'a gates_t = (int * bool * bool, 'a) map.

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
  op in_dom (x : 'a) (m : ('a,'b) map) = mem (dom m) x. 
  
  (** Valid gate predicate *)
  (** 
    A gate is valid if its corresponding truth table is completely defined, i.e., if it has rows that represent all possible entries (0,0/ 0,1 / 1,0/ 1,1).
  *)
  op valid_gates (n q : int) (gg:'a gates_t) =
    range n (n+q) true (fun g b,
                               b /\
                               in_dom (g, false, false) gg /\
                               in_dom (g, false, true) gg /\
                               in_dom (g, true, false) gg /\
                               in_dom (g, true, true) gg).

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
      (forall g i1 i2, n <= g < n + q => in_dom (g, i1, i2) (snd f)) /\
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
      range base (base + size) FMap.empty
    (fun (g:int) gg, fill g false false (fill g false true (fill g true false (fill g true true gg)))).
    
  (**
    The value of an initalised gate is the application of the function "f" given
    the number of the gate and the input bits.
  *)
  lemma get_initGates (base:int) size (f:int->bool->bool->'a) g a b :
      0 <= size =>
      (init_gates base size f).[(g, a, b)] = if base <= g < base + size then Some (f g a b) else None.
    proof.
      simplify init_gates FMap."_.[_]".
      elim/strongInduction size=> j le0_j hrange /=.
      case (0 < j)=> hj; last by smt ["Alt-Ergo"].
      rewrite range_ind_lazy /=; first by simplify => /#. 
      rewrite !FMap.get_set /=.
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
      0 <= size =>  base <= g < base + size => in_dom (g, a, b) (init_gates base size f).
    proof.
      simplify init_gates in_dom.    
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
  lemma gsch_correct : D.Correct() => GSch.Sch.Scheme.Correct().
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
      apply arrayP; split; rewrite size_sub /=; first 3 by smt ["Alt-Ergo"].
        rewrite size_map size_sub /=; first 2 by idtac=>/#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#. 
        by trivial.
        by idtac => /#.
        by idtac => /#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        simplify n => /#. 
      move => j hj.
      rewrite mapE.
        rewrite size_sub; first 2 by idtac => /#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#.
        exact hj.
      rewrite !get_sub; first 2 by idtac => /#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        simplify n => /#.
        exact hj.
        by idtac => /#.
        by idtac => /#.
        simplify evalComplete; rewrite appendInit_size /=; first by idtac => /#.
        (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#.
        exact hj.
      pose v := (GarbleTools.evalComplete _ _ _).[_].
      cut:= H9 (j + (n + q - m)) _; first by simplify n => /#. 
      progress => /#. 
  
    move => j boundJ.
    cut : j < n + q by idtac=>/#.
    cut : 0 <= j by idtac=>/#. clear boundJ.
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
        rewrite appendInit_size; first by idtac=>/#.
        simplify n => /#.
        idtac=>/#.
        smt ["Alt-Ergo"] tmo=5.
        (simplify inputEnc encode; rewrite size_offun max_ler; first by idtac => /#); simplify => /#.
        exact H2.
        smt ["Alt-Ergo"] tmo=10.  do 4!(congr); smt ["Alt-Ergo"] tmo=15.
          apply arrayP; split.
            rewrite size_sub; first 2 by done.
            (rewrite appendInit_size; first by idtac=>/#); simplify n => /#.
            (rewrite appendInit_size; first by idtac=>/#). simplify n;  smt. /#.
            
          done. exact kPos. rrewrite sub_complete. => /#. congr. congr. congr.  time smt tmo=30.  smt. smt. smt. smt. smt. smt. simplify extract;rewrite ! get_sub;smt.
      rewrite -/ar1 -/ar2.
      simplify extract.
      cut -> : (k - 1 + 1 = k) by smt.
      rewrite - ! hypRec;first 4 smt.
      simplify eval.
      rewrite get_initGates;first smt.
      simplify enc fst snd.
      cut ->: (getlsb (oget x.[(aa.[k], ar1.[aa.[k]])]) ^^
               getlsb (oget x.[(aa.[k], false)])) = ar1.[aa.[k]].
        case ar1.[aa.[k]]=> h;last smt.
        cut := H9 aa.[k] _;first clear h;smt.
        move : (getlsb (oget x.[(aa.[k], false)]))=> a.
        move : (getlsb (oget x.[(aa.[k], true)]))=> b.
        move => [_ [_ [HH _ ]]].
        by cut -> : b = ! a by smt;smt.
      cut ->: (getlsb (oget x.[(bb.[k], ar1.[bb.[k]])]) ^^
               getlsb (oget x.[(bb.[k], false)])) = ar1.[bb.[k]].
        case ar1.[bb.[k]]=> h;last smt.
        cut := H9 bb.[k] _;first clear h;smt.
        move : (getlsb (oget x.[(bb.[k], false)]))=> a.
        move : (getlsb (oget x.[(bb.[k], true)]))=> b.
        move => [_ [_ [HH _ ]]].
        by cut -> : b = ! a by smt;smt.
      case (n <= k < n + q); last smt (* absurd *).
      by rewrite /oget /=; do !rewrite -/(oget _); rewrite DKCHyp.

    (* Base case : prove main for the inputs by using encode and inputK definitions *)
    rewrite /ar1 /ar2 ! appendInit_get1;first 4 smt.
    rewrite -/ar1 -/ar2.
    simplify inputEnc GSch.Sch.Scheme.Input.encode GSch.Sch.Scheme.inputK fst.
    rewrite offunE /=; first by smt.
    rewrite FMap.get_filter /=.
    by (cut -> : 0 <= k < n = true by smt). 
    qed.

  (*******************************************************)
  (* Auxiliary lemmas concerning the validity of queries *)
  (*******************************************************)     

  lemma n_sizeG q: GSch.EncSecurity.queryValid_IND q => size q.`1.`2 = q.`1.`1.`1.`1.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1).
    by progress.
  qed.
      
  lemma n_sizeG' q: GSch.EncSecurity.queryValid_IND q => size q.`2.`2 = q.`2.`1.`1.`1.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1).
    by progress.
  qed.
    
  lemma le0_n q: GSch.EncSecurity.queryValid_IND q => 0 <= q.`1.`1.`1.`1.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1).
    by progress; smt.
  qed.
      
  lemma le0_n' q: GSch.EncSecurity.queryValid_IND q => 0 <= q.`2.`1.`1.`1.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1).
    by progress; smt.
  qed.

  lemma len_nqm q: GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= q.`1.`1.`1.`1 + q.`1.`1.`1.`3 - q.`1.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1).
    by progress; smt.
  qed.
      
  lemma len_nqm' q: GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= q.`2.`1.`1.`1 + q.`2.`1.`1.`3 - q.`2.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1).
    by progress; smt.
  qed.
  
  lemma lt0_m q: GSch.EncSecurity.queryValid_IND q => 0 < q.`1.`1.`1.`2. 
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`1.`1.`1).
    by progress.
  qed.

  lemma lt0_m' q: GSch.EncSecurity.queryValid_IND q => 0 < q.`2.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`2.`1.`1).
    by progress.
  qed.

  lemma leqm_q q: GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`2 <= q.`1.`1.`1.`3.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`1.`1.`1).
    by progress. 
  qed.

  lemma leqm_q' q: GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`2 <= q.`2.`1.`1.`3.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`2.`1.`1).
    by progress. 
  qed.
  
  lemma eqA_nq q: GSch.EncSecurity.queryValid_IND q => size q.`1.`1.`1.`4 = q.`1.`1.`1.`1 + q.`1.`1.`1.`3.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`1.`1.`1).
    by progress. 
  qed.

  lemma eqA_nq' q: GSch.EncSecurity.queryValid_IND q => size q.`2.`1.`1.`4 = q.`2.`1.`1.`1 + q.`2.`1.`1.`3.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`2.`1.`1).
    by progress. 
  qed.

  lemma eqB_nq q: GSch.EncSecurity.queryValid_IND q => size q.`1.`1.`1.`5 = q.`1.`1.`1.`1 + q.`1.`1.`1.`3.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`1.`1.`1).
    by progress. 
  qed.

  lemma eqB_nq' q: GSch.EncSecurity.queryValid_IND q => size q.`2.`1.`1.`5 = q.`2.`1.`1.`1 + q.`2.`1.`1.`3.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`2.`1.`1).
    by progress. 
  qed.

  lemma leq0_nqm q: GSch.EncSecurity.queryValid_IND q => 0 <= q.`1.`1.`1.`1 + q.`1.`1.`1.`3 - q.`1.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`1.`1.`1).
    by progress; smt.
  qed.

  lemma leq0_nqm' q: GSch.EncSecurity.queryValid_IND q => 0 <= q.`2.`1.`1.`1 + q.`2.`1.`1.`3 - q.`2.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`2.`1.`1).
    by progress; smt.
  qed.

  lemma leqn_nqm q: GSch.EncSecurity.queryValid_IND q => 0 <= q.`1.`1.`1.`1 <= q.`1.`1.`1.`1 + q.`1.`1.`1.`3 - q.`1.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`1.`1.`1).
    by progress; smt.
  qed.

  lemma leqn_nqm' q: GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= q.`2.`1.`1.`1 + q.`2.`1.`1.`3 - q.`2.`1.`1.`2.
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd. elim (q.`2.`1.`1).
    by progress; smt.
  qed.
  
  lemma le0_allA q i: GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 => 0 <= q.`1.`1.`1.`4.[i].
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma le0_allA' q i: GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 => 0 <= q.`2.`1.`1.`4.[i].
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.
  
  lemma le0_allB q i: GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 => 0 <= q.`1.`1.`1.`5.[i].
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H. 
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma le0_allB' q i: GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 => 0 <= q.`2.`1.`1.`5.[i].
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H. 
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma lt0_q q : GSch.EncSecurity.queryValid_IND q => 0 < q.`1.`1.`1.`3.
  proof.
    rewrite /GSch.EncSecurity.queryValid_IND /valid_plain /validInputs valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1).
    by progress.
  qed.

  lemma lt0_q' q : GSch.EncSecurity.queryValid_IND q => 0 < q.`2.`1.`1.`3.
  proof. 
    rewrite /GSch.EncSecurity.queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1).
    by progress.
  qed.

  lemma ltallB_nqm q i : GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1+q.`1.`1.`1.`3 => q.`1.`1.`1.`5.[i] < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 - q.`1.`1.`1.`2.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.
  
  lemma ltallB_nqm' q i : GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 => q.`2.`1.`1.`5.[i] < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 - q.`2.`1.`1.`2.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma ltallB_i q i : GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1+q.`1.`1.`1.`3 => q.`1.`1.`1.`5.[i] < i.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.
  
  lemma ltallB_i' q i : GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 => q.`2.`1.`1.`5.[i] < i.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.
  
  lemma ltallA_nqm q i : GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 => q.`1.`1.`1.`4.[i] < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 - q.`1.`1.`1.`2.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma ltallA_nqm' q i : GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1+q.`2.`1.`1.`3 => q.`2.`1.`1.`4.[i] < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 - q.`2.`1.`1.`2.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma ltallA_i q i : GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 => q.`1.`1.`1.`4.[i] < i.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma ltallA_i' q i : GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1+q.`2.`1.`1.`3 => q.`2.`1.`1.`4.[i] < i.
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma ltallA_allB q i : GSch.EncSecurity.queryValid_IND q => q.`1.`1.`1.`1 <= i < q.`1.`1.`1.`1 + q.`1.`1.`1.`3 => q.`1.`1.`1.`4.[i] < q.`1.`1.`1.`5.[i].
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`1.`1.`1); progress.
    cut ? : size q.`1.`2 = q.`1.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.
  
  lemma ltallA_allB' q i : GSch.EncSecurity.queryValid_IND q => q.`2.`1.`1.`1 <= i < q.`2.`1.`1.`1 + q.`2.`1.`1.`3 => q.`2.`1.`1.`4.[i] < q.`2.`1.`1.`5.[i].
  proof.
    move => valid.
    cut ? : GSch.EncSecurity.queryValid_IND q by exact valid.
    move : H.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput /valid_circuitP.
    simplify fst snd; elim (q.`2.`1.`1); progress.
    cut ? : size q.`2.`2 = q.`2.`1.`1.`1 by smt.
    move : H8; rewrite H13; progress.
    move : H11; rewrite H13; progress.
    move : H12; rewrite H13; progress.
    by smt.
  qed.

  lemma queryValid_validInputs q : GSch.EncSecurity.queryValid_IND q => validInputsP (fst q).
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs valid_wireinput.
    rewrite /validInputsP.
    simplify fst snd.
    by progress.
  qed.

  lemma queryValid_validInputs' q : GSch.EncSecurity.queryValid_IND q => validInputsP (snd q).
  proof.
    rewrite /queryValid_IND /valid_plain /validInputs ?valid_wireinput.
    rewrite /validInputsP.
    simplify fst snd.
    by progress.
  qed.

  lemma bound_nqm q : validInputsP q => q.`1.`1.`1 + q.`1.`1.`3 - q.`1.`1.`2 = bound.
  proof.
    rewrite /validInputsP /valid_circuitP. 
    simplify fst snd.
    by elim (q.`1.`1); progress. 
  qed.

  lemma in_dom_validInputs q g i1 i2 : validInputsP q => q.`1.`1.`1 <= g < q.`1.`1.`1 + q.`1.`1.`3 => in_dom (g, i1, i2) q.`1.`2.
  proof.
    rewrite /validInputsP /valid_circuitP.
    simplify fst snd.
    elim (q.`1.`1). progress. smt.
  qed.
  
  (******************)  
  (** Global values *)
  (******************) 

  (**
    Hybrid parameter
  *)
  module Hl = {
    var l : int
  }.
  
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

  (*******************************************************)
  (* Lemmas concerning the initialisation of the circuit *)
  (*******************************************************)

  lemma CircuitInit_lossless: islossless CircuitInit.init. 
  proof. by proc; while true (C.n + C.q - i); auto; smt. qed.

  lemma CircuitInitH (plain:fun_t*input_t):
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
      by auto; smt.
    auto=> //= &m p_plain; subst. 
    move: vIn; rewrite /validInputsP /valid_circuitP /fst /fst /fst /snd /snd.
    elim plain=> [fn] ii /=.
    elim (fn.`1). progress.
    rewrite size_offun.
    rewrite max_ler; first by smt.
    reflexivity.
    qed.

  equiv CircuitInitEquiv: CircuitInit.init ~ CircuitInit.init:
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
        split=> //=; first smt.
        split; first smt.
        split=> //.
        split=> //.
        split.
          move=> j j_bnd; case (i{2} = j).
            move=> i_j; subst; rewrite !get_set /=; first 3 smt.
            cut -> /=: (C.aa{2}.[j] = j) = false by smt.
            cut -> /=: (C.bb{2}.[j] = j) = false by smt.
            rewrite /evali /fst /snd /=.
            rewrite /evalComplete appendInit_getFinal //; first smt.
              by rewrite /extract //= !get_sub //; smt.
            rewrite /extract (_: j - 1 + 1 = j) //=; first smt.
              congr; congr; split=> //.
                by rewrite vWires; first smt.
                by rewrite vWires; first smt.
            rewrite -neqF=> j_neq_i; cut j_lt_i: j < i{2} by smt.
            rewrite get_set /=; first smt.
            rewrite vGates; first smt.
            cut ->: forall x, C.v{2}.[i{2} <- x].[C.aa{2}.[j]] = C.v{2}.[C.aa{2}.[j]] by smt.
            cut ->: forall x, C.v{2}.[i{2} <- x].[C.bb{2}.[j]] = C.v{2}.[C.bb{2}.[j]] by smt.
            cut ->: j = i{2} <=> false by smt. simplify. done.
        split=> //=.
          move=> j j_bnd; case (i{2} = j).
            by move=> i_j; subst; rewrite !get_set //=; first smt.
            rewrite -neqF=> j_neq_i; cut j_lt_i: j < i{2} by smt.
            rewrite get_set /=; first smt.
            rewrite vWires; first smt.
            cut ->: j = i{2} <=> false by smt. simplify. done.
    auto; move=> &1 &2 [eqP vIn] //=; subst.
    move: vIn; rewrite /validInputsP /validCircuitP /fst /fst /fst /snd /snd //=.
    elim (p{2})=> fn ii /=; subst.
    elim (fn)=> tt gg. 
    elim (tt) => n m q aa bb /=; subst.
    by progress; expect 11 smt.
  qed.

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
        C.n{1} <= g < C.n{1} + C.q{1} => in_dom (g,b1,b2) C.gg{1}) /\
      (forall g b1 b2,
        C.n{1} <= g < C.n{1} + C.q{1} => in_dom (g,b1,b2) C.gg{2}) /\
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
        do 11!(split; first smt).
        split; first by move=> g b1 b2 g_bnd; cut:= H7 g _=> //; case b1; case b2; smt.
        split; first by move=> g b1 b2 g_bnd; cut:= H17 g _; [smt|]; case b1; case b2.
        by smt.
    conseq (_: _ ==>
      (forall j,
        C.n{2} + C.q{2} - C.m{2} <= j < C.n{2} + C.q{2} =>
        C.v{1}.[j] = C.v{2}.[j]) /\
        size C.v{1} = C.n{2} + C.q{2} /\
        size C.v{2} = C.n{2} + C.q{2} /\
        (forall j, 0 <= j < C.n{2} => C.v{1}.[j] = C.x{1}.[j]) /\
        (forall j, 0 <= j < C.n{2} => C.v{2}.[j] = C.x{2}.[j])).
          by progress; expect 3 smt.
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
      progress; first 2 smt.
        rewrite !Array.get_set; first 2 smt.
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
          by case ((i = j){2}) => _; rewrite get_sub; smt.
          rewrite Array.get_set; first smt.
          by case ((i = j){2}) => _;
            rewrite /evali /evalComplete ?appendInit_get1; smt.
          rewrite Array.get_set;first smt.
          by case ((i = j){2}) => _;
            rewrite /evali /evalComplete ?appendInit_get1; smt.
    skip; progress; expect 10 smt.
  qed.
  
  (**
    Initialises the random values according to a boolean
    that decides if one is to use visible tokens or invisible ones.
  *)
  module RandomInit = {
    proc init(useVisible:bool): unit = {
      var i, tok1, tok2, v, trnd;

      R.t = offun (fun x, false) (C.n + C.q);
      R.xx = FMap.empty;
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

  (**********************************************************)
  (* Lemmas concerning the initialisation of the randomness *)
  (**********************************************************)
  
  lemma RandomInit_lossless: islossless RandomInit.init.
  proof.
    proc => //.
    while true (C.n + C.q - i).
      auto; progress; [smt| | |smt];
      expect 2 by cut:= Dword.dwordLsb_lossless; rewrite /weight /True=> ->.
    by auto; smt.
  qed.

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
        split; first smt.
        progress [-split].
        rewrite /validRand /validRand; elim (fst C.f{hr}) H1=> n m q aa bb [-> -> -> -> ->] /=.
        by split=> //= i [i_lb i_ub]; move: (H6 i _ _); first 2 smt.
      auto; progress.
        smt.
        case (j < i{hr})=> h.
          by rewrite !FMap.get_set_neq; expect 3 smt.
        cut ->: i{hr} = j by smt.
        rewrite !FMap.get_set /=.
        by case (useVisible{hr} && C.v{hr}.[j]).
        case (j < i{hr})=> h.
          by rewrite !FMap.get_set_neq; expect 3 smt.
        cut ->: i{hr} = j by smt.
        rewrite !FMap.get_set /=.
        by case (useVisible{hr} && C.v{hr}.[j])=> //=.
        case (j < i{hr})=> h.
          by rewrite !FMap.get_set_neq; expect 5 smt.
        cut ->: i{hr} = j by smt.
        rewrite !FMap.get_set /=.
        by case (useVisible{hr} && C.v{hr}.[j]); rewrite //= oget_some //=; smt.
        case (j < i{hr})=> h.
          by rewrite !FMap.get_set_neq; expect 3 smt.
        cut ->: i{hr} = j by smt.
        rewrite !FMap.get_set /=.
        by case (useVisible{hr} && C.v{hr}.[j]); rewrite //= oget_some //=; smt.
  qed.

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
          first 2 by rewrite !get_empty.
          by smt.
          by rewrite H6; first smt.
          by rewrite H7; first smt.
    auto; progress; rewrite H4 //=; first 5 smt.
    by rewrite !FMap.get_set; smt.
    by rewrite !FMap.get_set; smt.
    by smt.
  qed.
    
  pred t_xor (sup:int) (t1 t2 v:bool array) = forall i,
      0 <= i < sup =>
      t1.[i] = t2.[i] ^^ v.[i].

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
        do !(wp; rnd); skip; progress=> //;
          first 9 (rewrite /t_xor //=; progress=> //; try (cut := H i0); smt).
        rewrite ! FMap.get_set get_set;first smt.
        case (i{2} = j)=> h;[cut := H16;cut := H12;case v0=> hv0 /= |cut := H3 j v0 _].
          by rewrite h //=; smt.
          by rewrite h //=; smt.
          smt.
          smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j _]; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j _]; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j _]; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j _]; smt.
      swap{1} 4 1; do 2!(wp; rnd); wp; rnd (fun (x:bool), !x); skip;(progress=> //;first 6 smt).
        by rewrite FMap.set_set; smt.
        by simplify t_xor; progress; cut:= H i0; smt.
        smt.
        smt.
        smt.
        rewrite !FMap.get_set get_set; first smt.
        case (i{2} = j)=> h.
          subst; case v0=> h /=.
            by rewrite oget_some; smt.
            by smt.
          by cut:= H3 j v0; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j]; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j]; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[subst=> /= |cut := H4 j]; smt.
        by rewrite !FMap.get_set; case (i{2} = j)=> h;[ |cut := H4 j]; smt.
    wp; skip; progress=> //;simplify validRand validRand; smt.
  qed.

  (** Random generators *)
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
      R.xx = FMap.empty;
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

  lemma R_lossless (l' : topo_t): phoare [Rand.gen : l = l' /\ let (n,m,q,aa,bb) = l' in 1 < n /\ 0 < m /\ 0 < q /\ m <= q ==> true] = 1%r.
  proof.
    proc => //.
    while (0 <= i <= n+q) (n+q-i).
      by move => z; auto; smt.
    by auto; smt.
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
      G.pp = FMap.empty;
      G.randG = FMap.empty;
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

  module GameReal (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      
      query = ADV.gen_query();
      
      if (GSch.EncSecurity.queryValid_IND query) {
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

  module Game(S:Scheme_t, ADV:GSch.EncSecurity.Adv_IND_t) = {
    proc main() : bool = {
      var query,p,c,b,adv,ret;

      query = ADV.gen_query();
      if (GSch.EncSecurity.queryValid_IND query)
      {
        b = ${0,1};
        p = if b then snd query else fst query;
        c = S.enc(p);
        adv = ADV.get_challenge(c);
        ret = (b = adv);
      }
      else
        ret = ${0,1};
      return ret;
    }
  }.

  (* Gb from figure 7 *)
  module Garble1 : Scheme_t = {
    proc enc(p:fun_t*input_t) : funG_t*inputG_t*outputK_t = {
      CircuitInit.init(p);
      RandomInit.init(false);
      return
        (funG C.f R.xx, encode (inputK C.f R.xx) C.x, outputK C.f R.xx);
    }
  }.

  (*****************************************************)
  (* Lemmas concerning the PrivInd ~ GameReal equality *)
  (*****************************************************)
  
  lemma eqDefs (A<:GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}):
    equiv[Game(Garble1,A).main ~ GSch.EncSecurity.Game_IND(Rand,A).main:
    ={glob A} ==> ={res}].
  proof.
    proc; inline Game(Garble1,A).main.
    swap{2} 1 1; seq 1 1: (={query, glob A}); first by call (_: true).
    case (GSch.EncSecurity.queryValid_IND query{1}); last by rcondf{1} 1=> //; rcondf{2} 2; auto; smt.
    rcondt{1} 1=> //; rcondt{2} 2; first by auto.
    inline*. wp. call (_: true). wp.
      while (useVisible{1}= false /\ i0{1} = i{2} /\ (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst (if b{1} then snd query{1} else fst query{1})) /\ C.n{1} = n{2} /\ C.m{1} = m{2} /\ C.q{1} = q{2} /\ C.aa{1} = aa{2} /\ C.bb{1} = bb{2} /\ ={glob A, R.xx}).
        auto. (*progress. smt. smt. smt. smt. smt. smt. *)
      wp; while{1} (true) ((C.n + C.q - i){1});
        first by auto; smt.
    auto. progress. smt. smt. smt. smt.
    qed.
  
  lemma equivRealInd_aux (A <: GSch.EncSecurity.Adv_IND_t{Rand,GameReal,GarbleRealInit,R,C}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    equiv [ GameReal(A).garble ~ Game(Garble1,A).main :
      ={glob A} ==> ={res} ].
  proof.  
    move => AgenL AgetL.
    proc.
    seq 1 1 : (={query} /\ ={glob A}).
      by call (_ : true) => //; auto; smt.
    if; first by progress.
    auto.
    call (_ : true) => //.
    wp.
    inline Garble1.enc.
    inline GarbleRealInit.init.
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
      inline GarbleRealInit.garb'.
      inline GarbleRealInit.garb.
      wp.
      swap 13 -12.
      swap 26 -25.
      swap 39 -38.
      wp.
      simplify.
      do 3 ! rnd.
      skip.
      simplify funG funG fst snd t_xor.
      (progress;first 2 smt);last 4 smt. simplify.
      case (G.g{hr} = i)=> hi.
        rewrite hi !FMap.get_set get_initGates; first smt.
        cut -> /=: C.n{m} <= i < C.n{m} + C.q{m} by smt.
        rewrite !xor_true !xor_false /=.
        cut hneq : forall (x:bool), ((! x) = x) = false by smt.
        cut lem : forall u v, Some (enc R.xx{m} ((C.n{m}, C.m{m}, C.q{m}, C.aa{m}, C.bb{m}), C.gg{m}) i
          (u ^^ R.t{hr}.[C.aa{m}.[i]]) (v ^^ R.t{hr}.[C.bb{m}.[i]])) =
            Some (E (tweak i (R.t{hr}.[C.aa{m}.[i]]^^u) (R.t{hr}.[C.bb{m}.[i]]^^v))
              (oget R.xx{hr}.[(C.aa{m}.[i], u ^^ C.v{m}.[C.aa{m}.[i]])]) (oget R.xx{hr}.[(C.bb{m}.[i], v ^^ C.v{m}.[C.bb{m}.[i]])])
              (oget R.xx{hr}.[(i, (oget C.gg{m}.[(i, u^^C.v{m}.[C.aa{m}.[i]], v^^C.v{m}.[C.bb{m}.[i]])]))])).
          move => u v.
          simplify enc fst snd.
          rewrite !H3;first 4 by elim H2;smt.
          rewrite !H ;first 2 by elim H2;smt.
          rewrite !H4 ;first 3 by elim H2;smt.
          rewrite !(Bool.xorC false) !xor_false.
          cut xor_simpl : forall x y z, x ^^ (y ^^ z) ^^ y = x ^^ z
            by (move => x y z;case x;case y;case z;do rewrite /= ?(xor_true, xor_false) //).
          rewrite !xor_simpl.
          by do 2 !congr; rewrite Bool.xorC; [rewrite (Bool.xorC u) | rewrite (Bool.xorC v)]; rewrite Bool.xorA.
          (case (a = R.t{hr}.[C.aa{m}.[i]])=> ha;[rewrite ? ha|cut -> : a = !R.t{hr}.[C.aa{m}.[i]] by smt]);
          (case (b0 = R.t{hr}.[C.bb{m}.[i]])=> hb;[rewrite hb|cut -> : b0 = !R.t{hr}.[C.bb{m}.[i]] by smt]);rewrite ?hneq /=.
          by cut := lem false false;rewrite (H5 i) ?(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //;smt.
          by cut := lem false true;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //.
          by cut := lem true false;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //.
          by cut := lem true true;rewrite /enc !(fst_pair, snd_pair, (Bool.xorC false), xor_false, (Bool.xorC true), xor_true) //.
      cut h : forall aa bb, ((G.g{hr}, R.t{hr}.[C.aa{m}.[G.g{hr}]] ^^ aa, R.t{hr}.[C.bb{m}.[G.g{hr}]] ^^ bb) = (i, a, b0)) = false by smt.
      by rewrite !FMap.get_set !h /=;apply H7;smt.
    wp.
    call RandomGenClassicVisibleE.
    call CircuitInitEquiv.
    wp. rnd. skip.
    simplify funG funG fst.
    move => &1 &2 [? valid].
    simplify validInputsP valid_circuitP fst snd.
    progress.
      smt.
      by move : H2; case realL; first 2 by smt.  
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt. 
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt. 
      by move : H2; case realL; first 2 by smt. 
      by move : H2; case realL; first 2 by smt.
      by move : H2; case realL; first 2 by smt.
      by smt. 
      by smt.
      by smt.
      by smt.
      by cut := H16 i; smt.
      by smt.
      by smt.
      by smt.
      apply map_ext=> y.
      elim y=> i a b.
      by cut := H38 i a b; smt. 
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
        
      yy = $Dword.dword;
      yy = if rn then yy else oget R.xx.[(G.g, oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ bet)])];
      garb(yy, alpha, bet);
      return yy;
    }
    
    proc init() : unit = {
      var tok : word;

      G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
      G.pp = FMap.empty;
      G.randG = FMap.empty;
      G.a = 0;
      G.b = 0;

      G.g = C.n;
      while (G.g < C.n + C.q)
      {
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

  module GameFake (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
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

  lemma GarbleInitFakeL : islossless GarbleInitFake.init.
  proof.
    proc.
    while true (C.n + C.q - G.g).
      progress. inline*. auto. simplify. smt.
    by auto; smt.
  qed.

  (**********************************************)
  (* ALTERNATIVE VERSION - easy-independent one *)
  (**********************************************)

  module R' = {
    var t : bool array
    var vv : (int,word) map
    var ii : (int,word) map
  }.

  module RandomInit' = {
    proc init(useVisible:bool): unit = {
      var i, tok1, tok2, v, trnd;

      R'.t = offun (fun x, false) (C.n + C.q);
      R'.vv = FMap.empty;
      R'.ii = FMap.empty;

      i = 0;
      while (i < C.n + C.q) {
        trnd = ${0,1};
        v = if useVisible then C.v.[i] else false;
        trnd = if (i < C.n + C.q - C.m) then trnd else v;
        tok1 = $Dword.dwordLsb ( trnd);
        tok2 = $Dword.dwordLsb (!trnd);

        R'.t.[i] = trnd;

        R'.vv.[i] = tok1;
        R'.ii.[i] = tok2;

        i = i + 1;
      }
    } 
  }.

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
      auto; progress. smt. smt. smt. smt. smt. smt. rewrite ?get_set. case (i{2} = g); first by done. smt. rewrite ?get_set. case (i{2} = g); first by done. smt. rewrite ?get_set. smt. smt. simplify. case (g = i{2}) => hc. case (i{2} < C.n{2} + C.q{2} - C.m{2}) => hc'. reflexivity. smt. smt. rewrite ?get_set. case (i{2} = g) => hc. smt. smt. rewrite ?get_set. case (i{2} = g) => hc. smt. smt. rewrite size_set. exact H13. rewrite size_set. exact H16. 
    wp; skip; progress. smt. smt. smt. rewrite size_offun max_ler. smt. reflexivity. rewrite size_offun max_ler. smt. reflexivity. apply arrayP. split; first by smt. smt. rewrite H13. smt. reflexivity. rewrite H14. smt. reflexivity. rewrite H16. smt. done. rewrite H17. smt. done.
  qed.  

  module GarbleInitFake' = {
    
    proc init() : unit = {
      var tok : word;
      var wa, wb : word;
      var twe : word;
      
      G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
      G.pp = FMap.empty;
      G.randG = FMap.empty;
      G.a = 0;
      G.b = 0;

      G.g = C.n;
      while (G.g < C.n + C.q)
      {
        G.a = C.aa.[G.g];
        G.b = C.bb.[G.g];
        
        wa = oget R'.vv.[G.a];
        wb = oget R'.vv.[G.b];
        tok = oget R'.vv.[G.g];
        twe = tweak G.g (getlsb wa) (getlsb wb);
        G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

        wa = oget R'.vv.[G.a];
        wb = oget R'.ii.[G.b];
        tok = $Dword.dword;
        twe = tweak G.g (getlsb wa) (getlsb wb);
        G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

        wa = oget R'.ii.[G.a];
        wb = oget R'.vv.[G.b];
        tok = $Dword.dword;
        twe = tweak G.g (getlsb wa) (getlsb wb);
        G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

        wa = oget R'.ii.[G.a];
        wb = oget R'.ii.[G.b];
        tok = $Dword.dword;
        twe = tweak G.g (getlsb wa) (getlsb wb);
        G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;

        G.yy.[G.g] = tok;

        G.g = G.g + 1;
      }
    }
  }.
      
  lemma valid_inputs_allA f x k : validInputsP (f,x) => f.`1.`1 <= k < f.`1.`1 + f.`1.`3 => 0 <= f.`1.`4.[k] < f.`1.`1 + f.`1.`3.
  proof.
    simplify validInputsP valid_circuitP fst snd. 
    elim (f.`1) => n m q aa bb; simplify.
    progress; expect 2 by smt.
  qed.

  lemma valid_inputs_allB f x k : validInputsP (f,x) => f.`1.`1 <= k < f.`1.`1 + f.`1.`3 => 0 <= f.`1.`5.[k] < f.`1.`1 + f.`1.`3.
  proof.
    simplify validInputsP valid_circuitP fst snd. 
    elim (f.`1) => n m q aa bb; simplify.
    progress; expect 2 by smt.
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
      (*(forall g a b, C.n{1} <= g < (C.n + C.q){1} => mem (dom G.pp{1}) (g,a,b)) /\
      (forall g a b, C.n{1} <= g < (C.n + C.q){1} => mem (dom G.pp{2}) (g,a,b)) /\
      (forall g a b, !(C.n{1} <= g < (C.n + C.q){1}) => !mem (dom G.pp{1}) (g,a,b)) /\
      (forall g a b, !(C.n{1} <= g < (C.n + C.q){1}) => !mem (dom G.pp{2}) (g,a,b)).*)
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
    auto. progress. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. cut ->: getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. cut ->: getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> false by smt. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> false by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. cut ->: getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. cut ->: getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b <=> false by smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> false by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. cut ->: getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a <=> false by smt. simplify. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. cut ->: getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. cut ->: getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a <=> false by smt. cut ->: getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b <=> false by smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. smt. simplify. smt.
  
    (*rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. simplify. cut ? : G.g{2} <= C.n{2} by smt.*)

    rewrite mem_dom. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. by simplify. simplify. cut ->: getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. by simplify. simplify. smt. 

    rewrite mem_dom. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. by simplify. simplify. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. by simplify. simplify. smt. 

    rewrite mem_dom. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt. 

    rewrite mem_dom. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt. 

    rewrite mem_dom. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt. 

    rewrite mem_dom. rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt.

    rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt.
    
    rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{1}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{1}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{1}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{1}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt.

    rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt.

    rewrite ?get_set. simplify. case (G.g{2} = g) => hc. simplify. case (getlsb (oget R'.ii{2}.[C.aa{2}.[G.g{2}]]) = a) => ha. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. cut ->: getlsb (oget R'.vv{2}.[C.aa{2}.[G.g{2}]]) = a <=> true by smt. simplify. case (getlsb (oget R'.ii{2}.[C.bb{2}.[G.g{2}]]) = b) => hb. smt. cut ->: getlsb (oget R'.vv{2}.[C.bb{2}.[G.g{2}]]) = b <=> true by smt. simplify. smt. simplify. smt.

    by smt.
    by smt. 

    wp; skip; progress. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. move : H3. simplify validInputsP. simplify valid_circuitP. simplify fst snd. cut ->: C.f{1}.`1 = (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) by smt. simplify. progress. smt. smt. smt. smt. 
  qed.
  
  module GameFake' (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
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

  module GameFake'' (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
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
  
  lemma GameFake''_independent (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}) &m :
    islossless A.gen_query =>
    islossless A.get_challenge =>
    Pr[GameFake''(A).garble() @ &m: res] = 1%r / 2%r.
  proof.
    move => AgenLL AgetLL.
    byphoare => //; proc.
    seq 1 : true (1%r) (1%r/2%r) (0%r) _ true => //; first by call (_ : true).
    if; last by rnd;skip;smt.
    wp.
    swap 1 6.
    rnd ((=) adv).
    conseq (_ : true); first by progress;smt.
    call (_ : true) => //.
    wp. 
    inline GarbleInitFake'.init.
    while (true) (C.n + C.q - G.g).
      progress. wp. rnd. wp. rnd. wp. rnd. wp. skip. progress. smt. smt. smt. smt. 
    auto. 
    inline RandomInit'.init.
    while true (C.n + C.q - i).
      progress. auto. progress. smt. smt. smt. smt. 
    auto.
    inline CircuitInit.init.
    while true (C.n + C.q - i0).
      progress. auto. progress. smt.
    auto. progress.
    by smt.
    by smt.
    by smt.
  qed.
  
  lemma GameFake'_GameFake'' (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}) &m :
    equiv[GameFake'(A).garble ~ GameFake''(A).garble :
    ={glob A} ==> ={res}].
  proof.
    proc.
    seq 1 1 : (={glob A, query}).
      call (_ : true) => //.
    if; first by progress.
    wp.
    call (_ : true).
    wp.
    seq 4 4 : (
    (*Circuit initialisation equality*)
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
    (*Random initialisation equality*)
    ={R'.t} /\
      (forall g, 0 <= g < (C.n + C.q){1} => R'.vv.[g]{1} = R'.vv.[g]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => R'.ii.[g]{1} = R'.ii.[g]{2}) /\
      (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{1}) = !getlsb (oget R'.ii.[g]{1})) /\
      (forall g, 0 <= g < (C.n + C.q){1} => getlsb (oget R'.vv.[g]{2}) = !getlsb (oget R'.ii.[g]{2})) /\
      (0 <= C.m <= C.n + C.q /\
      Array.size R'.t = (C.n+C.q)){1}
    ).
    
    call Random'InitEquiv.
    call InitEquiv_rnd.
    auto; progress. smt. smt. smt. smt. smt. move : H9. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt.
    call GarbleInitFake'InitEquiv.
    skip. progress. smt. smt.
    apply map_ext. rewrite /(==) => x. elim x => g a b. case (C.n{2} <= g < C.n{2} + C.q{2}) => hc. rewrite H22. exact hc. reflexivity. rewrite H23. exact hc. rewrite H24. exact hc. reflexivity. 
    congr. apply fun_ext. rewrite /(==) => x. congr. rewrite ?get_filter. simplify. case (0 <= x < C.n{2}) => hc; last by done. rewrite H7. cut ? : C.n{2} < C.n{2} + C.q{2} by smt. smt. done.
    by auto.
  qed.
  
  (****************************************************************)
  (* ALTERNATIVE OF THE ALTERNATIVE VERSION WITH ALL WHILES MIXED *)
  (****************************************************************)

  module GameFakeMixedWhiles (ADV:GSch.EncSecurity.Adv_IND_t) = {

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

    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      var tok : word;
      var tok1, tok2, v, trnd;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
        real = ${0,1};
        p = if real then snd query else fst query;
        CircuitInit.init(p);

        (*random init*)
        R.t = offun (fun x, false) (C.n + C.q);
        R.xx = FMap.empty;
        (*/random init*)

        (*garble init*)
        G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
        G.pp = FMap.empty;
        G.randG = FMap.empty;
        G.a = 0;
        G.b = 0;
        G.g = 0;
        (*/garble init*)

        (*cycle [0;n[*)
        while (G.g < C.n) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = trnd;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R.t.[G.g] = trnd;
          
          R.xx.[(G.g, v)] = tok1;
          R.xx.[(G.g,!v)] = tok2;

          G.g = G.g + 1;
        }
        (*/cycle [0;n[*)

        (*cycle [n;n+q-m[*)
        while (G.g < C.n + C.q - C.m) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = trnd;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R.t.[G.g] = trnd;
          
          R.xx.[(G.g, v)] = tok1;
          R.xx.[(G.g,!v)] = tok2;

          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          
          garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
          tok = garb'(true, false,  true);
          tok = garb'(true,  true, false);
          G.yy.[G.g] = garb'(true,  true,  true);
          
          G.g = G.g + 1;
        }
        (*/cycle [n;n+q-m[*)

        (*cycle [n+q-m;n+q[*)
        while (G.g < C.n + C.q) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = v;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R.t.[G.g] = trnd;
          
          R.xx.[(G.g, v)] = tok1;
          R.xx.[(G.g,!v)] = tok2;

          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          
          garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
          tok = garb'(true, false,  true);
          tok = garb'(true,  true, false);
          G.yy.[G.g] = garb'(true,  true,  true);
          
          G.g = G.g + 1;
        }
        (*/cycle [n+q-m;n+q[*)

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
  
  module GameFake'MixedWhiles (ADV:GSch.EncSecurity.Adv_IND_t) = {

    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      var tok : word;
      var tok1, tok2, v, trnd;
      var wa, wb : word;
      var twe : word;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
        real = ${0,1};
        p = if real then snd query else fst query;
        CircuitInit.init(p);

        (*random init*)
        R'.t = offun (fun x, false) (C.n + C.q);
        R'.vv = FMap.empty;
        R'.ii = FMap.empty;
        (*/random init*)

        (*garble init*)
        G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
        G.pp = FMap.empty;
        G.randG = FMap.empty;
        G.a = 0;
        G.b = 0;
        G.g = 0;
        (*/garble init*)

        (*cycle [0;n[*)
        while (G.g < C.n) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = trnd;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R'.t.[G.g] = trnd;
          
          R'.vv.[G.g] = tok1;
          R'.ii.[G.g] = tok2;

          G.g = G.g + 1;
        }
        (*/cycle [0;n[*)

        (*cycle [n;n+q-m[*)
        while (G.g < C.n + C.q - C.m) {
          trnd = ${0,1};
          (*v = C.v.[G.g];*)
          trnd = trnd;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R'.t.[G.g] = trnd;
          
          R'.vv.[G.g] = tok1;
          R'.ii.[G.g] = tok2;

          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.vv.[G.b];
          tok = oget R'.vv.[G.g];
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.vv.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          G.yy.[G.g] = tok;
          
          G.g = G.g + 1;
        }
        (*/cycle [n;n+q-m[*)

        (*cycle [n+q-m;n+q[*)
        while (G.g < C.n + C.q) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = v;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R'.t.[G.g] = trnd;
          
          R'.vv.[G.g] = tok1;
          R'.ii.[G.g] = tok2;

          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.vv.[G.b];
          tok = oget R'.vv.[G.g];
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.vv.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          G.yy.[G.g] = tok;
          
          G.g = G.g + 1;
        }
        (*/cycle [n+q-m;n+q[*)
    
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

  module GameFake''MixedWhiles (ADV:GSch.EncSecurity.Adv_IND_t) = {

    proc garble () : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      var tok : word;
      var tok1, tok2, v, trnd;
      var wa, wb : word;
      var twe : word;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
        
        p = fst query;
        CircuitInit.init(p);

        (*random init*)
        R'.t = offun (fun x, false) (C.n + C.q);
        R'.vv = FMap.empty;
        R'.ii = FMap.empty;
        (*/random init*)

        (*garble init*)
        G.yy = Array.offun (fun x, (W.zeros)) (C.n + C.q);
        G.pp = FMap.empty;
        G.randG = FMap.empty;
        G.a = 0;
        G.b = 0;
        G.g = 0;
        (*/garble init*)

        (*cycle [0;n[*)
        while (G.g < C.n) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = trnd;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R'.t.[G.g] = trnd;
          
          R'.vv.[G.g] = tok1;
          R'.ii.[G.g] = tok2;

          G.g = G.g + 1;
        }
        (*/cycle [0;n[*)

        (*cycle [n;n+q-m[*)
        while (G.g < C.n + C.q - C.m) {
          trnd = ${0,1};
          (*v = C.v.[G.g];*)
          trnd = trnd;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R'.t.[G.g] = trnd;
          
          R'.vv.[G.g] = tok1;
          R'.ii.[G.g] = tok2;

          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.vv.[G.b];
          tok = oget R'.vv.[G.g];
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.vv.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          G.yy.[G.g] = tok;
          
          G.g = G.g + 1;
        }
        (*/cycle [n;n+q-m[*)

        (*cycle [n+q-m;n+q[*)
        while (G.g < C.n + C.q) {
          trnd = ${0,1};
          v = C.v.[G.g];
          trnd = v;
          tok1 = $Dword.dwordLsb ( trnd);
          tok2 = $Dword.dwordLsb (!trnd);
          
          R'.t.[G.g] = trnd;
          
          R'.vv.[G.g] = tok1;
          R'.ii.[G.g] = tok2;

          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.vv.[G.b];
          tok = oget R'.vv.[G.g];
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.vv.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.vv.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          wa = oget R'.ii.[G.a];
          wb = oget R'.ii.[G.b];
          tok = $Dword.dword;
          twe = tweak G.g (getlsb wa) (getlsb wb);
          G.pp.[(G.g, getlsb wa, getlsb wb)] = E twe wa wb tok;
          
          G.yy.[G.g] = tok;
          
          G.g = G.g + 1;
        }
        (*/cycle [n+q-m;n+q[*)
    
        c = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), offun (fun g, oget (filter (fun a b, 0 <= a < C.n) R'.vv).[g]) C.n, tt);
        
        adv = ADV.get_challenge(c);
        real = ${0,1};
        ret = (real = adv);
      }
      else {
        ret = ${0,1};
      }

      return ret;
    }
  }.
  
  
  lemma same_fakes (A<:GSch.EncSecurity.Adv_IND_t{C,R,R',G}):
    equiv[GameFakeMixedWhiles(A).garble ~ GameFake'MixedWhiles(A).garble :
    ={glob A} ==> ={res}].
  proof.
  proc.
  seq 1 1 : (={glob A,query}).
  call (_ : true) => //.
  if;first by progress.
  seq 2 2 : (
    ={glob A,query,real,p} /\ 
    (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1})
  ).
  wp;rnd;skip;smt.
  inline CircuitInit.init.
  seq 7 7 : (
     ={glob A,query,real,p,p0} /\ p0{1} = p{1} /\
     (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1}) /\
    C.f{1} = fst p{1} /\ C.f{2} = fst p{2} /\
    C.x{1} = snd p{1} /\ C.x{2} = snd p{2} /\
    size C.v{1} = C.n{2} + C.q{2} /\
    size C.v{2} = C.n{2} + C.q{2} /\
    ={C.n, C.m, C.q, C.aa, C.bb} /\ 
    (C.n{1}, C.m{1}, C.q{1},C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
    (C.n{2}, C.m{2}, C.q{2},C.aa{2}, C.bb{2}) = fst (fst p{2}) /\
    C.gg{1} = snd (fst p{1}) /\ 
    C.v{1} = offun (fun (_ : int) => false) (C.n{2} + C.q{2}) /\
    C.gg{2} = snd (fst p{2}) /\ 
    C.v{2} =offun (fun (_ : int) => false) (C.n{2} + C.q{2}) /\
    i{1} = 0 /\ i{2} = 0
  ); first by auto; progress; [by rewrite size_offun max_ler; first by smt | by rewrite size_offun max_ler; first by smt | smt | smt]. 
  seq 1 1 :  (
={glob A,query,real,p,p0,i} /\ p0{1} = p{1} /\ 
     (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1}) /\
    C.f{1} = fst p{1} /\ C.f{2} = fst p{2} /\
    C.x{1} = snd p{1} /\ C.x{2} = snd p{2} /\
    ={C.n, C.m, C.q, C.aa, C.bb} /\ 
    (C.n{1}, C.m{1}, C.q{1},C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
    (C.n{2}, C.m{2}, C.q{2},C.aa{2}, C.bb{2}) = fst (fst p{2}) /\
    C.gg{1} = snd (fst p{1}) /\ 
    (*C.v{1} = offun (fun (_ : int) => false) (C.n{2} + C.q{2}) /\*)
    C.gg{2} = snd (fst p{2}) /\ 
    (*C.v{2} =offun (fun (_ : int) => false) (C.n{2} + C.q{2}) /\*)
    (forall j, 0 <= j < C.n{1} + C.q{1} => C.v{1}.[j] = evali (fst p{1}) C.x{1} j) /\
    (forall j, 0 <= j < C.n{2} + C.q{2} => C.v{2}.[j] = evali (fst p{2}) C.x{2} j) /\
    C.v{1} = C.v{2} /\
    size C.v{2} = C.n{2} + C.q{2}
  ).
  while (={glob A, query, real, p, p0, i} /\ p0{1} = p{1} /\
  p{1} = (if real{1} then snd query{1} else fst query{1}) /\
  (GSch.EncSecurity.queryValid_IND query{1})/\
  C.f{1} = fst p{1} /\
  C.f{2} = fst p{2} /\
  C.x{1} = snd p{1} /\
  C.x{2} = snd p{2} /\
  size C.v{2} = C.n{2} + C.q{2} /\
  ={C.n, C.m, C.q, C.aa, C.bb} /\
  (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
  (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) = fst (fst p{2}) /\ size C.v{1} = C.n{2} + C.q{2} /\
  C.gg{1} = snd (fst p{1}) /\ C.gg{2} = snd (fst p{2}) /\ 0 <= i{1} <= C.n{2} + C.q{2} /\ C.v{1} = C.v{2} /\ (forall j, 0 <= j < i{1} => C.v{1}.[j] = evali (fst p{1}) C.x{1} j) /\ (forall j, 0 <= j < i{1} => C.v{2}.[j] = evali (fst p{2}) C.x{2} j)). wp; skip; progress. smt. smt. smt. smt. rewrite get_set. smt. case (j = i{2}) => hc. rewrite hc. reflexivity. smt. rewrite get_set. smt. case (j = i{2}) => hc. rewrite hc. reflexivity. smt. skip; progress. smt. smt. smt. smt. smt. 
  seq 8 9 :  (
     ={glob A,query,real,p,i} /\ G.g{1} = 0 /\ G.g{2} = 0 /\ 
     (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1}) /\
    C.f{1} = fst p{1} /\ C.f{2} = fst p{2} /\
    C.x{1} = snd p{1} /\ C.x{2} = snd p{2} /\
    ={C.n, C.m, C.q, C.aa, C.bb} /\
    size C.v{2} = C.n{2} + C.q{2} /\
    C.v{1} = C.v{2} /\
    (C.n{1}, C.m{1}, C.q{1},C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
    (C.n{2}, C.m{2}, C.q{2},C.aa{2}, C.bb{2}) = fst (fst p{2}) /\
    C.gg{1} = snd (fst p{1}) /\ 
    (*C.v{1} = offun (fun (_ : int) => false) (C.n{2} + C.q{2}) /\*)
    C.gg{2} = snd (fst p{2}) /\ 
    (*C.v{2} =offun (fun (_ : int) => false) (C.n{2} + C.q{2}) /\*)
    (forall j, 0 <= j < C.n{1} + C.q{1} => C.v{1}.[j] = evali (fst p{1}) C.x{1} j) /\
    (forall j, 0 <= j < C.n{2} + C.q{2} => C.v{2}.[j] = evali (fst p{2}) C.x{2} j)  /\
    C.v{1} = C.v{2} /\
     (R.t{1} = offun (fun (_ : int) => false) (C.n{1} + C.q{1})) /\
     (R'.t{2} = offun (fun (_ : int) => false) (C.n{2} + C.q{2})) /\ 
     (R.xx{1} = FMap.empty) /\
     (R'.vv{2} = FMap.empty) /\
     (R'.ii{2} = FMap.empty) /\
     (G.yy{1} = offun (fun (_ : int) => W.zeros) (C.n{1} + C.q{1})) /\
     (G.yy{2} = offun (fun (_ : int) => W.zeros) (C.n{2} + C.q{2})) /\
     (G.pp{1} = FMap.empty) /\  (G.pp{2} = FMap.empty) /\
     (G.randG{1} = FMap.empty) /\ (G.randG{2} = FMap.empty) /\
     (G.a{1} = 0) /\ (G.a{2} = 0) /\ 
     (G.b{1} = 0) /\ (G.b{2} = 0) /\ 
     size R.t{1} = C.n{1} + C.q{1} /\ size R'.t{2} = C.n{2} + C.q{2}
  ).
  wp;skip;progress. by rewrite size_offun max_ler; first by smt. by rewrite size_offun max_ler; first by smt. 

  wp; call (_ : true) => //; wp.
  
  while (={glob A, query, real, p} /\ G.g{1} = G.g{2} /\
    C.n{1} + C.q{1} - C.m{1} <= G.g{1} <= C.n{1} + C.q{1} /\
    (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1}) /\
    C.f{1} = fst p{1} /\
    C.f{2} = fst p{2} /\
    C.x{1} = snd p{1} /\
    C.x{2} = snd p{2} /\
    ={C.n, C.m, C.q, C.aa, C.bb} /\
    (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
    (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) = fst (fst p{2}) /\
    C.gg{1} = snd (fst p{1}) /\
    C.gg{2} = snd (fst p{2}) /\
    (forall (j : int),
      0 <= j < C.n{1} + C.q{1} => C.v{1}.[j] = evali (fst p{1}) C.x{1} j) /\
    (forall (j : int),
      0 <= j < C.n{2} + C.q{2} => C.v{2}.[j] = evali (fst p{2}) C.x{2} j) /\
    C.v{1} = C.v{2} /\
    (*G.yy{1} = offun (fun (_ : int) => W.zeros) (C.n{1} + C.q{1}) /\*)
    (*G.yy{2} = offun (fun (_ : int) => W.zeros) (C.n{2} + C.q{2}) /\*)
    G.pp{1} = G.pp{2} /\
    G.yy{1} = G.yy{2} /\
    G.randG{1} = FMap.empty /\
    G.randG{2} = FMap.empty /\
    (*G.a{1} = 0 /\
    G.a{2} = 0 /\
    G.b{1} = 0 /\
    G.b{2} = 0 /\*)
    (*(forall (j : int),
      (G.g{1} <= j) \/ (j < 0) => R'.vv{2}.[j] = None) /\*)
    (forall (j : int),
      0 <= j < G.g{1} =>
      R.t{1}.[j] = R'.t{2}.[j] /\
      C.v{1}.[j] = C.v{2}.[j] /\
      (*C.v{2}.[j] = R'.t{2}.[j] /\*)
      R.xx{1}.[(j, C.v{2}.[j])] = R'.vv{2}.[j] /\
      R.xx{1}.[(j, !C.v{2}.[j])] = R'.ii{2}.[j] /\
      getlsb (oget R.xx{1}.[(j, C.v{2}.[j])]) = getlsb (oget R'.vv{2}.[j]) /\
      getlsb (oget R.xx{1}.[(j, !C.v{2}.[j])]) = getlsb (oget R'.ii{2}.[j]) /\
      getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] /\
      getlsb (oget R'.ii{2}.[j]) = ! R'.t{2}.[j]) /\
    size R.t{1} = C.n{1} + C.q{1} /\ size R'.t{2} = C.n{2} + C.q{2}).

    inline*. auto. progress. smt. smt.

    cut ? : 0 <= G.g{2}. cut : 0 <= C.n{2} + C.q{2} - C.m{2}. move : H2. case (real{2}). smt. smt. smt.
    cut ? : 0 <= C.aa{2}.[G.g{2}] < G.g{2}. move : H2. case (real{2}) => hc. simplify fst snd. move => ?. cut ->: C.aa{2} = query{2}.`2.`1.`1.`4 by smt. smt. simplify fst snd. move => ?. cut ->: C.aa{2} = query{2}.`1.`1.`1.`4 by smt. smt. 
    cut ? : 0 <= C.bb{2}.[G.g{2}] < G.g{2}. move : H2. case (real{2}) => hc. simplify fst snd. move => ?. cut ->: C.bb{2} = query{2}.`2.`1.`1.`5 by smt. smt. simplify fst snd. move => ?. cut ->: C.bb{2} = query{2}.`1.`1.`1.`5 by smt. smt. 
  
    do(congr).  
  
    rewrite xor_false. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. rewrite H27. smt. reflexivity. 
    rewrite xor_false. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt. 
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt. 
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[C.aa{2}.[G.g{2}]] ^^ false) => hc'. smt. cut ->: C.v{2}.[G.g{2}] = C.v{2}.[C.aa{2}.[G.g{2}]] ^^ false <=> true by smt. by simplify. simplify. rewrite xor_false. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[C.bb{2}.[G.g{2}]] ^^ false) => hc'. smt. cut ->: C.v{2}.[G.g{2}] = C.v{2}.[C.bb{2}.[G.g{2}]] ^^ false <=> true by smt. by simplify. rewrite xor_false. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[C.bb{2}.[G.g{2}]] ^^ false) => hc'. simplify. smt. simplify. smt.  
    rewrite ?get_set. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}]) => hc. smt. trivial.
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt. 
    rewrite xor_true. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[C.aa{2}.[G.g{2}]]) => hc'. smt. simplify. cut ->: C.v{2}.[G.g{2}] = C.v{2}.[C.aa{2}.[G.g{2}]] <=> true by smt. by simplify. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = ! C.v{2}.[C.bb{2}.[G.g{2}]]) => hc'. by simplify. simplify. cut ->: C.v{2}.[G.g{2}] = ! C.v{2}.[C.bb{2}.[G.g{2}]] <=> true by smt. simplify. smt. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (C.v{2}.[G.g{2}]) _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.aa{2}.[G.g{2}]]) = ! C.v{2}.[C.aa{2}.[C.aa{2}.[G.g{2}]]]) => hc'.  rewrite -hc. by simplify. rewrite -hc.  by simplify. simplify. smt. 
    rewrite xor_false. rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.bb{2}.[G.g{2}]]) = C.v{2}.[C.bb{2}.[C.bb{2}.[G.g{2}]]]) => hc'. rewrite -hc. cut ->: (! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}] <=> false by smt. by simplify. rewrite -hc. cut ->: (! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}] <=> false by smt. by simplify. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!C.v{2}.[G.g{2}]) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.aa{2}.[G.g{2}]]) = ! C.v{2}.[C.aa{2}.[C.aa{2}.[G.g{2}]]]) => hc'. rewrite -hc. by simplify. rewrite -hc. by simplify. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.bb{2}.[G.g{2}]]) = ! C.v{2}.[C.bb{2}.[C.bb{2}.[G.g{2}]]]) => hc'. rewrite -hc. by simplify. rewrite -hc. by simplify. simplify. smt. 
    rewrite ?get_set. smt. smt. case (j = G.g{2}) => hc. reflexivity. smt.
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. simplify. case ((! C.v{2}.[j]) = C.v{2}.[j]) => hc'. smt. reflexivity. simplify. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. by simplify. simplify. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. simplify. cut ->: (! C.v{2}.[j]) = C.v{2}.[j] <=> false by smt. by simplify. simplify. smt.
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. by simplify. simplify. smt. 
    rewrite ?get_set. smt. case (G.g{2} = j) => hc. rewrite hc. simplify. smt. cut ->: j = G.g{2} <=> false by smt. simplify. smt.
    rewrite ?get_set. smt. simplify. case (G.g{2} = j) => hc. rewrite hc. simplify. smt. cut ->: j = G.g{2} <=> false by smt. simplify. smt.
    rewrite size_set. exact H7.
    rewrite size_set. exact H8.
  
    while (={glob A, query, real, p} /\ G.g{1} = G.g{2} /\
    C.n{1} <= G.g{1} <= C.n{1} + C.q{1} - C.m{1} /\
    (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1}) /\
    C.f{1} = fst p{1} /\
    C.f{2} = fst p{2} /\
    C.x{1} = snd p{1} /\
    C.x{2} = snd p{2} /\
    ={C.n, C.m, C.q, C.aa, C.bb} /\
    (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
    (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) = fst (fst p{2}) /\
    C.gg{1} = snd (fst p{1}) /\
    C.gg{2} = snd (fst p{2}) /\
    (forall (j : int),
      0 <= j < C.n{1} + C.q{1} => C.v{1}.[j] = evali (fst p{1}) C.x{1} j) /\
    (forall (j : int),
      0 <= j < C.n{2} + C.q{2} => C.v{2}.[j] = evali (fst p{2}) C.x{2} j) /\
    C.v{1} = C.v{2} /\
    (*G.yy{1} = offun (fun (_ : int) => W.zeros) (C.n{1} + C.q{1}) /\*)
    (*G.yy{2} = offun (fun (_ : int) => W.zeros) (C.n{2} + C.q{2}) /\*)
    G.pp{1} = G.pp{2} /\
    G.yy{1} = G.yy{2} /\
    G.randG{1} = FMap.empty /\
    G.randG{2} = FMap.empty /\
    (*G.a{1} = 0 /\
    G.a{2} = 0 /\
    G.b{1} = 0 /\
    G.b{2} = 0 /\*)
    (*(forall (j : int),
      (G.g{1} <= j) \/ (j < 0) => R'.vv{2}.[j] = None) /\*)
    (forall (j : int),
      0 <= j < G.g{1} =>
      R.t{1}.[j] = R'.t{2}.[j] /\
      C.v{1}.[j] = C.v{2}.[j] /\
      (*C.v{2}.[j] = R'.t{2}.[j] /\*)
      R.xx{1}.[(j, C.v{2}.[j])] = R'.vv{2}.[j] /\
      R.xx{1}.[(j, !C.v{2}.[j])] = R'.ii{2}.[j] /\
      getlsb (oget R.xx{1}.[(j, C.v{2}.[j])]) = getlsb (oget R'.vv{2}.[j]) /\
      getlsb (oget R.xx{1}.[(j, !C.v{2}.[j])]) = getlsb (oget R'.ii{2}.[j]) /\
      getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] /\
      getlsb (oget R'.ii{2}.[j]) = ! R'.t{2}.[j]) /\
    size R.t{1} = C.n{1} + C.q{1} /\ size R'.t{2} = C.n{2} + C.q{2}).

    inline*. auto. progress. smt. smt.

    cut ? : 0 <= G.g{2}. cut : 0 <= C.n{2} + C.q{2} - C.m{2}. move : H2. case (real{2}). smt. smt. smt.
    cut ? : 0 <= C.aa{2}.[G.g{2}] < G.g{2}. move : H2. case (real{2}) => hc. simplify fst snd. move => ?. cut ->: C.aa{2} = query{2}.`2.`1.`1.`4 by smt. smt. simplify fst snd. move => ?. cut ->: C.aa{2} = query{2}.`1.`1.`1.`4 by smt. smt. 
    cut ? : 0 <= C.bb{2}.[G.g{2}] < G.g{2}. move : H2. case (real{2}) => hc. simplify fst snd. move => ?. cut ->: C.bb{2} = query{2}.`2.`1.`1.`5 by smt. smt. simplify fst snd. move => ?. cut ->: C.bb{2} = query{2}.`1.`1.`1.`5 by smt. smt. 
  
    do(congr). 
  
    rewrite xor_false. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb trndL _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. rewrite H27. smt. reflexivity. 
    rewrite xor_false. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb trndL _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt. 
    rewrite xor_false. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb trndL _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt. 
    rewrite xor_false. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb trndL _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. rewrite -hc. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}]) => hc'. smt. by cut ->: C.v{2}.[G.g{2}] = C.v{2}.[G.g{2}] <=> true by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => R.xx{1}.[(j, C.v{2}.[j])] = R'.vv{2}.[j] by smt. rewrite H26. smt. reflexivity. 
    rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[C.bb{2}.[G.g{2}]] ^^ false) => hc'. smt. cut ->: C.v{2}.[G.g{2}] = C.v{2}.[C.bb{2}.[G.g{2}]] ^^ false <=> true by smt. by simplify. rewrite xor_false. simplify. smt.  
    rewrite ?get_set. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}]) => hc. smt. trivial.
    rewrite xor_false. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb trndL _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. rewrite H27. smt. reflexivity.
    rewrite xor_true. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb trndL _). exact H14. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = C.v{2}.[C.aa{2}.[G.g{2}]]) => hc'. smt. simplify. cut ->: C.v{2}.[G.g{2}] = C.v{2}.[C.aa{2}.[G.g{2}]] <=> true by smt. by simplify. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[G.g{2}]) = ! C.v{2}.[C.bb{2}.[G.g{2}]]) => hc'. by simplify. simplify. cut ->: C.v{2}.[G.g{2}] = ! C.v{2}.[C.bb{2}.[G.g{2}]] <=> true by smt. simplify. smt. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (trndL) _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite get_set. smt. rewrite get_set. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_false. rewrite get_set. smt. rewrite get_set. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite oget_some. rewrite (Dword.lsb_dwordLsb (trndL) _). exact H14. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.aa{2}.[G.g{2}]]) = ! C.v{2}.[C.aa{2}.[C.aa{2}.[G.g{2}]]]) => hc'.  rewrite -hc. by simplify. rewrite -hc.  by simplify. simplify. smt. 
    rewrite xor_false. rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.bb{2}.[G.g{2}]]) = C.v{2}.[C.bb{2}.[C.bb{2}.[G.g{2}]]]) => hc'. rewrite -hc. cut ->: (! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}] <=> false by smt. by simplify. rewrite -hc. cut ->: (! C.v{2}.[G.g{2}]) = C.v{2}.[G.g{2}] <=> false by smt. by simplify. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.aa{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.aa{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. smt. case (C.bb{2}.[G.g{2}] = G.g{2}) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H16. reflexivity. cut ->: G.g{2} = C.bb{2}.[G.g{2}] <=> false by smt. simplify. cut ? : forall (j : int), 0 <= j < G.g{2} => getlsb (oget R'.ii{2}.[j]) = !R'.t{2}.[j] by smt. cut ? : forall (j : int), 0 <= j < G.g{2} => R.t{1}.[j] = R'.t{2}.[j] by smt. rewrite H26. smt. smt.
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.aa{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.aa{2}.[G.g{2}]]) = ! C.v{2}.[C.aa{2}.[C.aa{2}.[G.g{2}]]]) => hc'. rewrite -hc. by simplify. rewrite -hc. by simplify. simplify. smt. 
    rewrite xor_true. rewrite ?get_set. simplify. case (G.g{2} = C.bb{2}.[G.g{2}]) => hc. simplify. case ((! C.v{2}.[C.bb{2}.[G.g{2}]]) = ! C.v{2}.[C.bb{2}.[C.bb{2}.[G.g{2}]]]) => hc'. rewrite -hc. by simplify. rewrite -hc. by simplify. simplify. smt. 
    rewrite ?get_set. smt. smt. case (j = G.g{2}) => hc. reflexivity. smt.
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. simplify. case ((! C.v{2}.[j]) = C.v{2}.[j]) => hc'. smt. reflexivity. simplify. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. by simplify. simplify. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. simplify. cut ->: (! C.v{2}.[j]) = C.v{2}.[j] <=> false by smt. by simplify. simplify. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. by simplify. simplify. smt. 
    rewrite ?get_set. smt. case (G.g{2} = j) => hc. rewrite hc. simplify. smt. cut ->: j = G.g{2} <=> false by smt. simplify. smt.
    rewrite ?get_set. smt. case (G.g{2} = j) => hc. rewrite hc. simplify. smt. cut ->: j = G.g{2} <=> false by smt. simplify. smt.
    rewrite size_set. exact H7.
    rewrite size_set. exact H8.

    while (={glob A, query, real, p} /\ G.g{1} = G.g{2} /\
    0 <= G.g{1} <= C.n{1} /\
    (p{1} = if real{1} then snd query{1} else fst query{1}) /\
    (GSch.EncSecurity.queryValid_IND query{1}) /\
    C.f{1} = fst p{1} /\
    C.f{2} = fst p{2} /\
    C.x{1} = snd p{1} /\
    C.x{2} = snd p{2} /\
    ={C.n, C.m, C.q, C.aa, C.bb} /\
    (C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}) = fst (fst p{1}) /\
    (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) = fst (fst p{2}) /\
    C.gg{1} = snd (fst p{1}) /\
    C.gg{2} = snd (fst p{2}) /\
    (forall (j : int),
      0 <= j < C.n{1} + C.q{1} => C.v{1}.[j] = evali (fst p{1}) C.x{1} j) /\
    (forall (j : int),
      0 <= j < C.n{2} + C.q{2} => C.v{2}.[j] = evali (fst p{2}) C.x{2} j) /\
    C.v{1} = C.v{2} /\
    (*G.yy{1} = offun (fun (_ : int) => W.zeros) (C.n{1} + C.q{1}) /\*)
    (*G.yy{2} = offun (fun (_ : int) => W.zeros) (C.n{2} + C.q{2}) /\*)
    G.pp{1} = G.pp{2} /\
    G.yy{1} = G.yy{2} /\
    G.randG{1} = FMap.empty /\
    G.randG{2} = FMap.empty /\
    (*G.a{1} = 0 /\
    G.a{2} = 0 /\
    G.b{1} = 0 /\
    G.b{2} = 0 /\*)
    (*(forall (j : int),
      (G.g{1} <= j) \/ (j < 0) => R'.vv{2}.[j] = None) /\*)
    (forall (j : int),
      0 <= j < G.g{1} =>
      R.t{1}.[j] = R'.t{2}.[j] /\
      C.v{1}.[j] = C.v{2}.[j] /\
      (*C.v{2}.[j] = R'.t{2}.[j] /\*)
      R.xx{1}.[(j, C.v{2}.[j])] = R'.vv{2}.[j] /\
      R.xx{1}.[(j, !C.v{2}.[j])] = R'.ii{2}.[j] /\
      getlsb (oget R.xx{1}.[(j, C.v{2}.[j])]) = getlsb (oget R'.vv{2}.[j]) /\
      getlsb (oget R.xx{1}.[(j, !C.v{2}.[j])]) = getlsb (oget R'.ii{2}.[j]) /\
      getlsb (oget R'.vv{2}.[j]) = R'.t{2}.[j] /\
      getlsb (oget R'.ii{2}.[j]) = ! R'.t{2}.[j]) /\
    size R.t{1} = C.n{1} + C.q{1} /\ size R'.t{2} = C.n{2} + C.q{2}).

    inline*. auto. progress. smt. smt.

    rewrite ?get_set. smt. smt. case (j = G.g{2}) => hc. done. smt.
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. simplify. cut ->: (! C.v{2}.[j]) = C.v{2}.[j] <=> false by smt. by simplify. simplify. smt.
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. by simplify. simplify. smt. 
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. simplify. cut ->: (! C.v{2}.[j]) = C.v{2}.[j] <=> false by smt. by simplify. simplify. smt.
    rewrite ?get_set. simplify. case (G.g{2} = j) => hc. simplify. rewrite hc. by simplify. simplify. smt. 
    rewrite ?get_set. smt. case (G.g{2} = j) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb trndL _). exact H13. reflexivity. cut ->: j = G.g{2} <=> false by smt. simplify. smt.
    rewrite ?get_set. smt. case (G.g{2} = j) => hc. rewrite hc. simplify. rewrite (Dword.lsb_dwordLsb (!trndL) _). exact H15. reflexivity. cut ->: j = G.g{2} <=> false by smt. simplify. smt.
    rewrite size_set. exact H7.
    rewrite size_set. exact H8.

    skip. progress.
    smt.
    by rewrite ?get_empty.
    by rewrite ?get_empty.
    by rewrite ?get_empty.
    by rewrite ?get_empty.
    smt.
    smt.
    smt.
    cut ->: g_R = C.n{2} by smt. case (real{2}) => hc. cut ->: C.n{2} = query{2}.`2.`1.`1.`1 by smt. cut ->: C.q{2} = query{2}.`2.`1.`1.`3 by smt. cut ->: C.m{2} = query{2}.`2.`1.`1.`2 by smt. smt. cut ->: C.n{2} = query{2}.`1.`1.`1.`1 by smt. cut ->: C.q{2} = query{2}.`1.`1.`1.`3 by smt. cut ->: C.m{2} = query{2}.`1.`1.`1.`2 by smt. smt.
    by smt.
    by smt.
    simplify encode. congr. apply fun_ext. rewrite /(==). move => x. congr. simplify inputK. case (real{2}) => hc. simplify fst snd. cut ->: query{2}.`2.`1.`1 = (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) by smt. simplify. rewrite ?get_filter. simplify. case (0 <= x < C.n{2}) => hc'; last by done. cut ->: query{2}.`2.`2.[x] = C.v{2}.[x]. cut := H27 x. rewrite hc. simplify. simplify fst snd. move => hevali. rewrite hevali. smt. simplify evali. simplify fst snd. cut ->: query{2}.`2.`1.`1 = (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) by smt. simplify. simplify extract evalComplete. rewrite appendInit_get1. smt. smt. reflexivity. smt. simplify fst snd. cut ->: query{2}.`1.`1.`1 = (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) by smt. simplify. rewrite ?get_filter. simplify. case (0 <= x < C.n{2}) => hc'; last by done. cut ->: query{2}.`1.`2.[x] = C.v{2}.[x]. cut := H27 x. rewrite hc. simplify. simplify fst snd. move => hevali. rewrite hevali. smt. simplify evali. simplify fst snd. cut ->: query{2}.`1.`1.`1 = (C.n{2}, C.m{2}, C.q{2}, C.aa{2}, C.bb{2}) by smt. simplify. simplify extract evalComplete. rewrite appendInit_get1. smt. smt. reflexivity. smt. 
    smt.
    by auto.
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
      G.pp = FMap.empty;
      G.randG = FMap.empty;
      G.a = 0;
      G.b = 0;

      G.g = C.n;
      while (G.g < C.n + C.q)
      {
        G.a = C.aa.[G.g];
        G.b = C.bb.[G.g];

        garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);
        
        tok = garb'(G.a <= l, true,  false);
        tok = garb'(G.b <= l,  false, true);
        G.yy.[G.g] = garb'(G.a <= l,  true,  true);

        if (G.a <= l < G.b /\ C.gg.[(G.g, !C.v.[G.a], false)] = C.gg.[(G.g, !C.v.[G.a], true)]) {
          garb(G.yy.[G.g], true, false);
        }
        
        G.g = G.g + 1;
      }
    }
  }.

  module GameHybrid (ADV:GSch.EncSecurity.Adv_IND_t) = {
      
    proc garble (l : int) : bool = {
      var query : GSch.EncSecurity.query_IND;
      var p : GSch.EncSecurity.Encryption.plain;
      var ret : bool;
      var topo : topo_t;
      var real, adv : bool;
      var c : funG_t*inputG_t*outputK_t;
      
      query = ADV.gen_query();
        
      if (GSch.EncSecurity.queryValid_IND query) {
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

  (**********************************************************)
  (* Lemmas concerning the GameHybrid_0 ~ GameReal equality *)
  (**********************************************************)

  equiv RinitE:
      RandomInit.init ~ RandomInit.init:
        ={useVisible, glob C} /\
        (0 <= C.m <= C.n + C.q){1} /\
        (fst C.f = (C.n, C.m, C.q, C.aa, C.bb)){1} ==>
        ={glob R} /\
        (validRand C.f R.xx){1} /\
        (Array.size R.t = (C.n+C.q)){1}.
    proof. by conseq (_: ={useVisible,glob C} ==> ={glob R}) RandomInitH; sim. qed.
  
  lemma GameReal_GameHybrid0 (A <: GSch.EncSecurity.Adv_IND_t{Rand,R,GameReal,GameHybrid}): 
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
      GSch.EncSecurity.queryValid_IND query{1} /\
      (*(p{1} = if real{1} then snd query{1} else fst query{1}) /\*)
      (*((C.f{1}, C.x{1}) = if real{1} then snd query{1} else fst query{1}) /\*)
      (*p{1} = (C.f{1}, C.x{1}) /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\*)
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
      inline*. auto. progress. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. smt. smt. 
      cut ->: C.aa{2}.[G.g{2}] <= -1 <=> false by smt. cut ->: C.bb{2}.[G.g{2}] <= -1 <=> false by smt. simplify. rewrite ?get_set. simplify. case (G.g{2} = k) => hc. simplify. case (R.t{2}.[C.aa{2}.[G.g{2}]] ^^ true = a) => ha. case (R.t{2}.[C.bb{2}.[G.g{2}]] ^^ true = b) => hb. simplify. congr. congr. smt. smt. congr. rewrite H3. smt. reflexivity. simplify. cut ->: R.t{2}.[C.bb{2}.[G.g{2}]] ^^ false = b <=> true by smt. simplify. congr. smt. smt. congr. rewrite H3. smt. reflexivity. simplify. cut ->: R.t{2}.[C.aa{2}.[G.g{2}]] ^^ false = a <=> true by smt. simplify. case (R.t{2}.[C.bb{2}.[G.g{2}]] ^^ true = b) => hb. congr. congr. rewrite H3. smt. reflexivity. rewrite H3. smt. reflexivity. rewrite H3. smt. reflexivity. cut ->: R.t{2}.[C.bb{2}.[G.g{2}]] ^^ false = b <=> true by smt. simplify. congr. rewrite H3. smt. reflexivity. rewrite H3. smt. reflexivity. rewrite H3. smt. reflexivity. simplify. rewrite H4. smt. reflexivity. 
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H5. exact H18. reflexivity.
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H6. smt. reflexivity.
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H7. exact H18. reflexivity.
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H8. smt. reflexivity.
    wp.
    call RandomInitEquiv.
    call CircuitInitEquiv.
    auto; progress.
    by smt.
    move : H4. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt. 
    move : H4. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt. 
    move : H4. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt.
    case (b = v_R.[k]) => hb. rewrite hb. rewrite H10. smt. reflexivity. cut ->: b = !v_R.[k] by smt. rewrite H11. smt. reflexivity.
    by rewrite get_empty.
    by rewrite get_empty.
    by rewrite get_empty.
    by rewrite get_empty.
    apply map_ext. rewrite /(==) => x. elim x => k a b. case (n_R <= k < g_R) => hk. rewrite H23. exact hk. reflexivity. smt. 
    simplify encode. congr. apply fun_ext. rewrite /(==) => x. congr. simplify inputK. simplify fst snd. rewrite ?get_filter. simplify. case (0 <= x < n_R) => hc. rewrite H22. smt. reflexivity. reflexivity. 
  qed.    

  (**************************************************************)
  (* Lemmas concerning the GameHybrid_bound ~ GameFake equality *)
  (**************************************************************)

  lemma eqnqm_bound n m q aa bb gg x : validInputsP (((n,m,q,aa,bb),gg), x) => bound = n + q - m.
  proof.
    simplify validInputsP.
    simplify valid_circuitP.
    simplify fst snd.
    progress.
    by rewrite -H4.
  qed.

  lemma allBlt_bound n m q aa bb gg x k : validInputsP (((n,m,q,aa,bb),gg), x) => n <= k < n + q => bb.[k] < bound.
  proof.
    simplify validInputsP.
    simplify fst valid_circuitP. 
    progress. 
    smt.
  qed.  

  lemma allAlt_bound n m q aa bb gg x k : validInputsP (((n,m,q,aa,bb),gg), x) => n <= k < n + q => aa.[k] < bound.
  proof.
    simplify validInputsP.
    simplify fst valid_circuitP. 
    progress. 
    smt.
  qed.  
  
  lemma GameFake_GameHybridbound (A <: GSch.EncSecurity.Adv_IND_t{Rand,R,GameReal,GameHybrid}): 
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
      GSch.EncSecurity.queryValid_IND query{1} /\
      (*(p{1} = if real{1} then snd query{1} else fst query{1}) /\*)
      (*((C.f{1}, C.x{1}) = if real{1} then snd query{1} else fst query{1}) /\*)
      (*p{1} = (C.f{1}, C.x{1}) /\
      C.f{1} = ((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}) /\*)
      validInputsP (((C.n{1}, C.m{1}, C.q{1}, C.aa{1}, C.bb{1}), C.gg{1}), C.x{1}) /\
      C.n{1} <= G.g{1} <= C.n{1} + C.q{1} /\
      l{2} = bound-1 /\
      l{2} = l0{2} /\
      (forall k b, 0 <= k < C.n{1} + C.q{1} => R.xx{1}.[(k,b)] = R.xx{2}.[(k,b)]) /\
      (forall k a b, C.n{1} <= k < G.g{1} => G.pp{1}.[(k,a,b)] = G.pp{2}.[(k,a,b)]) /\
      (forall k a b, k < C.n{1} => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{1}.[(k,a,b)] = None) /\
      (forall k a b, k < C.n{1} => G.pp{2}.[(k,a,b)] = None) /\
      (forall k a b, G.g{1} <= k => G.pp{2}.[(k,a,b)] = None)).
      inline*. auto. progress. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. by cut : false by smt. smt. smt. 
      cut ->: C.aa{2}.[G.g{2}] <= bound-1 <=> true by smt. cut ->: C.bb{2}.[G.g{2}] <= bound-1 <=> true by smt. simplify. rewrite ?get_set. simplify. case (G.g{2} = k) => hc. simplify. case (R.t{2}.[C.aa{2}.[G.g{2}]] ^^ true = a) => ha. case (R.t{2}.[C.bb{2}.[G.g{2}]] ^^ true = b) => hb. simplify. congr. congr. smt. smt. congr. rewrite ?H3. smt. smt. reflexivity. simplify. cut ->: R.t{2}.[C.bb{2}.[G.g{2}]] ^^ false = b <=> true by smt. simplify. congr. smt. smt. simplify. cut ->: R.t{2}.[C.aa{2}.[G.g{2}]] ^^ false = a <=> true by smt. simplify. case (R.t{2}.[C.bb{2}.[G.g{2}]] ^^ true = b) => hb. congr. congr. rewrite H3. smt. reflexivity. rewrite H3. smt. reflexivity. rewrite H3. smt. cut ->: R.t{2}.[C.bb{2}.[G.g{2}]] ^^ false = b <=> true by smt. simplify. congr. rewrite H3. smt. reflexivity. rewrite H3. smt. reflexivity. simplify. rewrite H4. smt. reflexivity. 
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H5. exact H18. reflexivity.
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H6. smt. reflexivity.
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H7. exact H18. reflexivity.
    rewrite ?get_set. simplify. cut ->: G.g{2} = k <=> false by smt. simplify. rewrite H8. smt. reflexivity.
    wp.
    call RandomInitEquiv.
    call CircuitInitEquiv.
    auto; progress.
    by smt.
    move : H4. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt. 
    move : H4. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt. 
    move : H4. simplify validInputsP valid_circuitP. simplify fst snd. progress. smt.
    case (b = v_R.[k]) => hb. rewrite hb. rewrite H10. smt. reflexivity. cut ->: b = !v_R.[k] by smt. rewrite H11. smt. reflexivity.
    by rewrite get_empty.
    by rewrite get_empty.
    by rewrite get_empty.
    by rewrite get_empty.
    apply map_ext. rewrite /(==) => x. elim x => k a b. case (n_R <= k < g_R) => hk. rewrite H23. exact hk. reflexivity. smt. 
    simplify encode. congr. apply fun_ext. rewrite /(==) => x. congr. simplify inputK. simplify fst snd. rewrite ?get_filter. simplify. case (0 <= x < n_R) => hc. rewrite H22. smt. reflexivity. reflexivity. 
  qed. 

  (*****************)
  (* DKC ADVERSARY *)
  (*****************)
      
  require import DInterval.  

  op l : int.
  axiom l_pos : 0 <= l < bound.

  module DKC_Adv (D : DKC_t, Adv_IND : GSch.EncSecurity.Adv_IND_t) : Adv_DKC_t = {
    var c : bool
    
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
    
    proc query (rn : bool, alpha : bool, betha : bool) : query * word = {
      var twe : word;
      var gamma, pos : bool;
      var i,j : int;
      var ki, kj, zz : word;
      
      twe = tweak G.g (R.t.[G.a] ^^ alpha) (R.t.[G.b] ^^ betha);
      gamma = C.v.[G.g] ^^ oget C.gg.[(G.g, C.v.[G.a] ^^ alpha, C.v.[G.b] ^^ betha)];

      pos = (G.a = l);
      i = if G.a = l then 2*G.b + bti (R.t.[G.b] ^^ betha) else 2*G.a + bti (R.t.[G.a] ^^ alpha);
      j = $[2*(G.g + C.n + C.q)..2*(G.g + C.n + C.q)+1];
      j = if rn then j else 2*G.g + (bti (R.t.[G.g] ^^ gamma));

      (ki,kj,zz) = D.encrypt((i,j,pos,twe));

      G.pp.[(G.g, R.t.[G.a] ^^ alpha, R.t.[G.b] ^^ betha)] = zz;

      if (G.a = l) {
        R.xx.[(G.b, C.v.[G.b] ^^ betha)] = ki;
      }
      else {
        R.xx.[(G.a, C.v.[G.a] ^^ alpha)] = ki;
      }

      if (rn) {
        R.xx.[(G.g, C.v.[G.g] ^^ gamma)] = kj;
      }

      return ((i,j,pos,twe), kj);
    }

    proc gen_queries (lsb:bool) : query array = {
      var query_ind : GSch.EncSecurity.query_IND;
      var i : int;
      var p : GSch.EncSecurity.Encryption.plain;
      var queries : query array;
      var q : query;
      var yy : word;
      
      (*initialisation of query array?*)
      queries = ArrayExt.empty;
      
      query_ind = Adv_IND.gen_query();
      if (GSch.EncSecurity.queryValid_IND query_ind) {
        c = ${0,1};
        p = if c then snd query_ind else fst query_ind;
        CircuitInit.init(p);
        RandomInit.init(true);

        G.g = C.n;
        while (G.g < C.n + C.q) {
          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          R.t.[l] = !lsb;

          if (G.a = l) {
            (q, yy) = query(false,true,false);
            queries = q :: queries;
          }
          (q, yy) = query(false,true,true);
          queries = q :: queries;
          
          if (G.b = l) {
            (q, yy) = query(false,false,true);
            queries = q :: queries;
          }
          (q, yy) = query(true,true,true);
          queries = q :: queries;
          G.yy.[G.g] = yy;
        }
      }
      
      return (queries);
    }
    
    proc get_challenge (answers : answer array) : bool = {
      var yy : word;
      var ciph : funG_t*inputG_t*outputK_t;
      var c' : bool;
      var ret : bool;

      if (0 < size answers) {
        G.g = C.n;
        while (G.g < C.n + C.q) {
          G.a = C.aa.[G.g];
          G.b = C.bb.[G.g];
          garb(oget R.xx.[(G.g, C.v.[G.g])], false, false);

          if (G.a <> l /\ G.b <> l) {
            garb'(G.a <= l, true, false);
            garb'(G.b <= l, false, true);
            yy = garb'(G.a <= l, true, true);

            if (G.a <= l < G.b /\ C.gg.[(G.g, !C.v.[G.a], false)] = C.gg.[(G.g, !C.v.[G.a], true)]) {
              garb(yy, true, false);
            }
            else {
              if (G.a = l) {
                garb'(false, false, true);
              }
              else {
                garb'(true, true, false);
              }
            }

            if (C.gg.[(G.g, !C.v.[G.a], false)] = C.gg.[(G.g, !C.v.[G.a], true)]) {
              garb(G.yy.[G.g], true, false);
            }
          }
        }
      
        ciph = (((C.n, C.m, C.q, C.aa, C.bb), G.pp), encode (inputK C.f R.xx) C.x, tt);
        c' = Adv_IND.get_challenge(ciph);
        ret = (c = c');
      }
      else {
        ret = ${0,1};
      }
      return ret;
    }
  }.

  lemma GameHybrid_l_sim (A <: GSch.EncSecurity.Adv_IND_t{DKC_Adv}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKCSecurity.DKC, DKC_Adv(DKCSecurity.DKC, A)).game:
        ={glob A} /\ l{1} = l /\ !b{2} ==> res{1} = !res{2}].
  proof. admit. qed.

  lemma GameHybrid_l1_sim (A <: GSch.EncSecurity.Adv_IND_t):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    equiv [ GameHybrid(A).garble ~ DKCSecurity.Game(DKCSecurity.DKC, DKC_Adv(DKCSecurity.DKC, A)).game:
        ={glob A} /\ l{1} = l-1 /\ b{2} ==> ={res}].
  proof. admit. qed.

  lemma GameHybrid_l_sim_pr (A <: GSch.EncSecurity.Adv_IND_t {DKC_Adv}) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
    Pr[GameHybrid(A).garble(l)@ &m: res] =
    Pr[DKCSecurity.Game(DKCSecurity.DKC, DKC_Adv(DKCSecurity.DKC, A)).game(false)@ &m: !res].
  proof. by move=> AgenLL AgetL; byequiv (GameHybrid_l_sim A _ _). qed. 

  lemma GameHybrid_l1_sim_pr (A <: GSch.EncSecurity.Adv_IND_t {DKC_Adv}) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
    Pr[GameHybrid(A).garble(l-1)@ &m: res] =
    Pr[DKCSecurity.Game(DKCSecurity.DKC, DKC_Adv(DKCSecurity.DKC, A)).game(true)@ &m: res].
  proof. by move=> AgenLL AgetL; byequiv (GameHybrid_l1_sim A _ _). qed. 
    
  print GSch.EncSecurity.
    
  lemma gsch_is_ind (A <: GSch.EncSecurity.Adv_IND_t) (Adv <: Adv_DKC_t) &m:
    `|2%r * Pr[GSch.EncSecurity.Game_IND(Rand,A).main()@ &m:res] - 1%r| =
    2%r * (bound)%r * `|2%r * Pr[GameDKC(Adv).main()@ &m:res] - 1%r|.
      proof. admit. qed.

  lemma gsch_is_sim (A <: GSch.EncSecurity.Adv_SIM_t {R}) (Adv <: Adv_DKC_t) &m:
    islossless A.gen_query =>
    islossless A.get_challenge =>
    `|2%r * Pr[GSch.EncSecurity.Game_SIM(Rand,GSch.EncSecurity.SIM(Rand),A).main()@ &m:res] - 1%r| <=
    2%r * (bound)%r * `|2%r * Pr[GameDKC(Adv).main()@ &m:res] - 1%r|.
  proof. admit. qed.
      
end SomeGarble.
export SomeGarble.
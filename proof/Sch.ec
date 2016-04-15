(** Abstraction of a garbling scheme *)

require import Array.
require import Int.
require import Pair.
require import FMap. (*import OptionGet.*)
require import Option.

(**
  A garbling scheme is a cryptographic primitive used to 
  transform (garble) circuits, so that one is still able to
  correctly evaluate them.

  A garbling scheme is a 5-tuple of algorithms:
    - Gb : circuit -> rand -> garbled circuit
    - En : input -> in_key -> garbled input
    - De : garbled output -> out_key -> output
    - Ev : garbled circuit -> garbled input -> garbled output
    - ev : circuit -> input -> output

  Attached to the formalisation of a garbling scheme is the definition
  of the leakage of the circuit. This leakage defines the security aim. It
  can be the topology of the circuit, its number of gates or even all the
  circuit.
*)
theory Scheme.

  (** 
    The Input theory defines the input and all the orther elements attatched
    to it, namely, the key used to garble the input, the garbled input, the 
    encoding function and the length of it.
  
    Needs to be separated for OT compatibility.
  *)
  theory Input.

    (** Inputs of the circuit *)
    type input_t.

    (** Key used to garble the input *)
    type inputK_t.

    (** Garbled input *)
    type inputG_t.

    (** En algorithm *)
    op encode : inputK_t -> input_t -> inputG_t.

    (** Length of the garbled input *)
    op inputG_len : inputG_t -> int. (* for VC proofs *)
  end Input.
  export Input.

  (** Circuit *)
  type fun_t.

  (** Garbled circuit *)
  type funG_t.

  (** Output of the circuit *)
  type output_t.

  (** Key used to decode the garbled output *)
  type outputK_t.
  
  (** Garbled output *)
  type outputG_t.

  (** Leakage of the circuit *)
  type leak_t.

  (** Randomness used to garble a circuit *)
  type rand_t.

  (** Validity of the elements of the garbling scheme*)
  op validCircuit : fun_t -> bool.
  op validInputs : fun_t -> input_t -> bool.
  pred validRand : (fun_t, rand_t).
  op valid_outG : outputK_t -> outputG_t -> bool. (* VC change *)
  
  (** Leakage function *)
  op phi : fun_t -> leak_t.

  (* ev function *)
  op eval : fun_t -> input_t -> output_t.

  (** Gb function *)
  op funG : fun_t -> rand_t -> funG_t.

  (** Generation of the key to garble inputs *)
  op inputK : fun_t -> rand_t -> inputK_t.

  (** Generation of the key to decode outputs *)
  op outputK : fun_t -> rand_t -> outputK_t.

  (** De function *)
  op decode : outputK_t -> outputG_t -> output_t.

  (** Ev function *)
  op evalG : funG_t -> inputG_t -> outputG_t.

  (** Leakage functions *)
  op pi_sampler : leak_t * output_t  -> fun_t * input_t.

  (** Correctness of a garbling scheme: ev f x = De(d, Ev(Gb(r,f), En(e,x))) *)
  pred Correct (x:unit) = forall r fn i,
    validInputs fn i =>
    validRand fn r =>
    eval fn i =
     let fG = funG fn r in
     let iK = inputK fn r in
     let oK = outputK fn r in
     let iG = encode iK i in
     decode oK (evalG fG iG).

end Scheme.
export Scheme.
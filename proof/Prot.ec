(** Abstraction of a two-party MPC protocols *)
(** We use it to abstract both OT and SFE *)

(**
   Let f be the function to be evaluated in the two-party protocol.

   A two-party protocol is viewed formally as a tuple (\Pi,ev), where
   \Pi = (\Pi_1, \Pi_2) and ev = (ev_1, ev_2).

   ev_1 and ev_2 are deterministic functions that compute the output of
   both parties at the end of the protocol.

   \Pi_1 and Pi_2 describe the cryptographic protocol that will be executed 
   between parties P1 and P2. Party P1 executes \Pi_1 and Party P2 executes \Pi_2.
   Each party will interactively run \Pi_i on current stage, incoming message and 
   produce an outgoing message, a local output and a decision to halt and continue.
   The initial stage of a party is its local input.

   In the papper "Foundations of Garbled Circuits", a two-party protocol is seen
   only as \Pi = (\Pi_1, \Pi_2), with the same meaning of our view. They describe 
   also two functions: View, that outputs the view of some party (messages exchanged
   and the leakage of information about the input of the other party), and Out, that
   returns the local output of some party. Out is similar to our definition of ev and
   the View function is included in the execution of the protocol, i.e., we include the
   conversation of the protocol in its execution.
*)

theory Protocol.

  (** Party types *)
  (** 
     Each party will have an input, and output and a leakage type.
     The randomness is defined explicitly, therefore defined as a parameter.
     The leakage of some party will parametrise the security of the protocol.
  *)

  (** Party 1 types *)
  (** Randomness of party 1 *)
  type rand1_t.

  (** Input of party 1 *)
  type input1_t.

  (** Output of party 1 *)
  type output1_t.

  (** Leakage of party 1 *)
  type leak1_t.

  (** Party 2 types *)
  (** Randomness of party 2 *)
  type rand2_t.

  (** Input of party 2 *)
  type input2_t.

  (** Output of party 2 *)
  type output2_t.

  (** Leakage of party 2 *)
  type leak2_t.

  (** Functionality of the procotol *)
  (** 
     Taking as input the local (private) inputs of both parties, outputs
     the local output of both parties. 
     Similar to (ev_1(I_1,I_2), ev_2(I_1,I_2)). This function defines ev_1 as 
     fst (f(I_1,I_2)) and ev_2 as snd (f(I_1,I_2)).
  *)
  op f : input1_t -> input2_t -> output1_t * output2_t.

  (** Execution trace and views *)
  type conv_t.

  (** Validity predicates *)
  (** 
     Predicates that atests if two inputs and random values are valid to the protocol. 
     A two-party protocol deals with a specific types, therefore the predicate is needed.
     For example, if our two-party protocol is defined over bit strings, this predicate 
     atests if the bit strings have a valid size.
  *)
  op validInputs : input1_t -> input2_t -> bool.
  pred validRands : (input1_t,input2_t,rand1_t, rand2_t).

  (** Protocol execution & outcomes *)
  (**
     Party P1 inputs to the predicate its input and some random value 
     (recall randomness define explicitly).
     Party P2 inputs to the predicate its input and some random value 
     (recall randomness define explicitly).
    
     The execution of the protocol outputs the execution trace and the 
     views of both parties (conv_t) and the local ouput of both parties 
     (output1_t * output2_t).
  *)
  op prot : input1_t -> rand1_t -> input2_t -> rand2_t -> conv_t * (output1_t * output2_t).

  (** Leakage functions *)
  (**
     Leakage tell us what info, from secret data, is expected to be public. (e.g. lengths) 
  *)
  op phi1 : input1_t -> leak1_t.
  op phi2 : input2_t -> leak2_t.
end Protocol.
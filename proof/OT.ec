(** Abstraction of an oblivious transfer protocol *)

require import Array.

(**
  An oblivious transfer protocol is a particular case of a two-party 
  protocol.

  In an oblivious transfer protocol some party sends potentially many
  information to other party but does not know which part (if any) of
  the information has been sent.

  We define the theory for the array extension of a 1 out of 2 OT protocol. 
  In a 1 out of 2 OT protocol, the sender has two messages m_0 and m_1 and
  the receiver has a selection bit b. The receiver wants to receive
  m_b without the sender learning b while the sender wants to ensure that 
  the receiver receives only one of the two messages.

  In the natural extension to arrays, the sender has an array of messages
  and the receiver has selection bit string s. This extension is nothing
  more than multiple executions of the original protocol.
*)

theory OT.
  (** The parametrizable attributes of n simultaneous 1 out of 2 OT protocol *)
  type msg_t.

  (** We hardwire the input types to be bool array for the picker,
     and (msg_t * msg_t) array for the holder. *)
  op max_size: int.

  (** Party 1 types *)
  type rand1_t.

  (** Party 2 types *)
  type rand2_t.

  (** Execution trace and views *)
  type conv_t.

  (** Protocol execution & outcomes *)
  op prot : bool array -> rand1_t -> (msg_t * msg_t) array -> rand2_t -> conv_t * (msg_t array * unit).
end OT.
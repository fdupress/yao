(** Security definitions for an OT protocol *)

require import Pair.
require import Array.
require import Int.

require import OT.
require import Prot.
require import ProtSec.

(**
  Being an OT protocol a particular case of a two-party protocol,
  it inherits the same security definitions and properties seen
  for two-party protocols.

  Therefore, we just need to instantiate the security of a two-party
  protocol to the special case of an OT protocol.
*)

theory OTSecurity.
  clone import OT.

  (** 
    Instantiation of the security of a genertic two-party protocol to
    an OT protocol. 
    
    We hardwire the OT functionality and valid inputs definition.
    These fix the correctness of any OT protocol. 
  *)
  clone ProtSecurity as OTPSec with
    type Protocol.rand1_t = rand1_t,
    type Protocol.input1_t = bool array,
    type Protocol.output1_t = msg_t array,
    type Protocol.leak1_t = int, (* size of choice word *)
    type Protocol.rand2_t = rand2_t,
    type Protocol.input2_t = (msg_t*msg_t) array,
    type Protocol.output2_t = unit,
    type Protocol.leak2_t = int, (* number of messages *)
    type Protocol.conv_t = conv_t,

    op Protocol.f (i1:bool array) (i2:(msg_t * msg_t) array) =
      (offun (fun k, if i1.[k] then snd i2.[k] else fst i2.[k]) (size i2), ()),

    op Protocol.phi1 (i1:input1_t) = size i1,

    op Protocol.phi2 (i2:input2_t) = size i2,

    op Protocol.validInputs (i1:bool array) (i2:(msg_t * msg_t) array) =
      0 < size i1 <= max_size /\ size i1 = size i2,

    pred Protocol.validRands i1 i2 r1 r2 = true,

    op Protocol.prot = prot.
end OTSecurity.
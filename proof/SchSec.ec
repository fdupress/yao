(** IND and SIM security definitions for a garbling scheme *)

require import Distr.
require import Pair.
require import Array.
require import Int.

require        EncSec.
require        Sch.

(**
  A garbling scheme can be seen as an ecryption scheme. In fact:
    - enc <=> Gb
    - plain <=> circuit
    - cipher <=> garbled circuit
    - rand <=> rand
    - leak <=> leak

  Therefore, we can instantiate the already described IND and SIM
  security definitions for encryption schemes to the special case
  of garbling schemes.
*)
theory SchSecurity.
  clone import Sch.

  (**
    Instantiation of the security of a encryption scheme to the case of
    a garbling scheme. 
    
    The encryption/garbling procedure is defined as a distribution
    induced by an abstract distribution on the randomness. 

    Randomness depends only on the function.
  *)
  clone EncSec.EncSecurity with
    type Encryption.rand = rand_t,
    type Encryption.plain = fun_t * input_t,
    type Encryption.cipher = funG_t * inputG_t * outputK_t,
    type Encryption.leakage = leak_t * output_t,
    type Encryption.randgenin = leak_t,

    op Encryption.enc (m:fun_t * input_t) (r:rand_t) =
      (funG (fst m) r, encode (inputK (fst m) r) (snd m), outputK (fst m) r),

    op Encryption.valid_plain(p : plain) =
      validInputs (fst p) (snd p),

    op Encryption.leak(p : plain) = 
      (phi (fst p), eval (fst p) (snd p)),

    op Encryption.randfeed (p:plain) = phi (fst p),
    op Encryption.pi_sampler = pi_sampler.

end SchSecurity.
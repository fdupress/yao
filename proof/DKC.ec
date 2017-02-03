(** Abstraction of a dual-key cipher (DKC) encryption scheme *)

require import Int.
require import Distr.
require import Bool.
require import Pair.

(**
  Informally, a DKC encryption scheme is a scheme where some
  message is ciphered using two keys. One needs both keys to
  cipher and both keys to decipher.

  Formally, a DKC encryption scheme is made of two functions
    - E -> a permutation defined on the type of the plaintext,
    using a tweak and two keys, that produce a ciphertext
    - D -> a permutation defined on the type of the ciphertext,
    using a tweak and two keys, that produce a plaintext
*)
theory DKCScheme.

  (* "Global" type of the DKC. 
  For a better formalisation, we are defining a DKC theory
  in which all the types involved will be the same.

  All the types should be equal to this DKC type "t" (that will
  be define to be of "word" type).

  With this, we can keep the rest of the theory intact.
  *)
  type t.

  (** Tweak *)
  type tweak_t = t.

  (** Keys *)
  type keys_t = t.  
  
  (** Plaintext *)
  type msg_t = t.
  
  (** Ciphertext *)
  type cipher_t = t.

  (** Permutation E *)
  op E: tweak_t -> keys_t -> keys_t -> msg_t -> cipher_t.

  (** Permutation D *)
  op D: tweak_t  -> keys_t -> keys_t -> cipher_t -> msg_t.
  
  (** Correctness assertion *)
  (**
    The DKC encryption scheme is correct iff 
    D(t,k1,k2,E(t,k1,k2,x)) = x.

    Shouldn't this be in the security definitions?
  *)
  pred Correct (t:unit) = forall t k1 k2 x, D t k1 k2 (E t k1 k2 x) = x.
end DKCScheme.
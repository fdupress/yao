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

  (** Tweak *)
  type tweak_t.

  (** Keys *)
  type key1_t.
  type key2_t.

  (** Keys distribution *)
  op key1_t_d : key1_t distr.
  op key2_t_d : key2_t distr.
  
  (** Plaintext *)
  type msg_t.

  (** Ciphertext *)
  type cipher_t.

  (** Permutation E *)
  op E: tweak_t -> key1_t -> key2_t -> msg_t -> cipher_t.

  (** Permutation D *)
  op D: tweak_t  -> key1_t -> key2_t -> cipher_t -> msg_t.

  (** Correctness assertion *)
  (**
    The DKC encryption scheme is correct iff 
    D(t,k1,k2,E(t,k1,k2,x)) = x.

    Shouldn't this be in the security definitions?
  *)
  pred Correct (t:unit) = forall t k1 k2 x, D t k1 k2 (E t k1 k2 x) = x.
end DKCScheme.
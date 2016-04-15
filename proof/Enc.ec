(** Abstraction of an encryption scheme *)

(**
  An encryption scheme is a 3-tuple of algorithms:
    - keygen : rand
    - enc : rand -> plain -> cipher
    - dec : rand -> cipher -> plain

  In our case, we are not interested in the dec function, since
  we are only interested in defining security for an encryption and
  we do not consider its correctness.

  We consider the information that is leaked by the plaintext (typically, 
  its size) and a the seed to randomness generation. Additionally, we consider 
  a function that, given the leakage of a plaintext, tries to recover it.

  This theory might seem a bit out of context. However, it will be used to
  define a garbling scheme and its security properties, since we can consider
  a garbling scheme an encryption scheme: the "transformation" of the circuit
  can be seen as its "encryption", somewhat.
*)
theory Encryption.

  (** Types of the encryption scheme *)
  (** Randomness (key) *)
  type rand.

  (** Plaintext *)
  type plain.

  (** Ciphertext *)
  type cipher.

  (** Leakage *)
  type leakage.

  (** Seed of the random generator *)
  type randgenin.

  (** Operations of an encryption scheme *)
  (** Encryption function *)
  op enc:plain -> rand -> cipher.

  (** Valid plaintext predicate *)
  op valid_plain:plain -> bool.

  (** Plaintext leakage function *)
  op leak:plain -> leakage.

  (** Random generator seed generation *)
  op randfeed:plain -> randgenin.

  (** Leakage inverter *)
  op pi_sampler:leakage -> plain.
end Encryption.
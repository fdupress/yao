(** Abstraction of a projective garbling scheme *)

require import Array.
require import Pair.
require import Int.

require        Sch.
require import ArrayExt.

(**
  A typicall approach is to define garbling schemes for boolean circuits,
  being the En function defined to encode a list of tokens with the same
  size of the input. The En function uses the bits of the input to select
  from the list of tokens (X0_1,X1_1, ..., X0_N, X1_N) the subvector
  X = (Xx1_1, ..., Xxn_n).

  A boolean garbling scheme is projective if for all circuits f, inputs
  x and x' and X = En(e,x) and X' = En(e,x'), if x_i = x'_i then
  |X_i| = |X'_i| and X_i == X'_i. 
*)
theory ProjScheme.
  type token_t.

 (** Instantiation of a garbling scheme with the correct types *)
  clone import Sch with
    type Scheme.Input.input_t = bool array,
    type Scheme.Input.inputK_t = (token_t * token_t) array,
    type Scheme.Input.inputG_t = token_t array,

    op Scheme.Input.encode (iK:inputK_t) (x:input_t) =
      offun (fun k, (if x.[k] then snd else fst) iK.[k]) (size iK).
  import Scheme.

  (** The above defined scheme is, indeed, projective *)
  lemma is_projective iK x x':
    x = x' =>
    encode iK x = encode iK x'.
  proof. by move => Hxx'; rewrite arrayP; smt. qed.

  (** We provide some lemmas describing additinal properties of 
      the encoding function *)
  (**
    encode (iK1 @ iK2) (i1 @ i2) = (encode iK1 i1) @ (encode iK2 i2)
  *)
  lemma encode_cat iK1 iK2 i1 i2:
   size iK1 = size i1 => size iK2 = size i2 =>
   encode (iK1 || iK2) (i1 || i2) =
   ((encode iK1  i1) || (encode iK2 i2)). 
  proof.
    delta=> H1 H2 /=. 
    rewrite !H1 !H2 !size_append.
    apply arrayP; split.
      rewrite size_offun; first by smt.
    move=> k.
    rewrite size_offun.
    move=> Hk.
    case (k < size i1)=> Hcase.
      rewrite get_append_left; first by smt.
      rewrite offunifE //= get_append_left; first by smt.
      rewrite (get_append_left iK1 iK2 k); first by smt.
      by rewrite offunifE //=; first by smt.
      timeout 60.
      rewrite get_append_right; first by rewrite ?size_mkarray ?List.size_map; smt.
      timeout 30.
      rewrite size_offun.
      rewrite offunifE //= get_append_right; first by smt.
      rewrite (get_append_right iK1 iK2 k); first by smt.
      rewrite max_ler in Hk; first by smt. 
      rewrite Hk. simplify.
    by rewrite H1 offunifE //=; first by smt.
  qed.

  (**
    encode iK.[0 .. |i1|] i1 = (encode iK (i1 @ i2)).[0 .. |i1|]
  *)
  lemma encode_take iK i1 i2:
   size iK = size (i1||i2)%ArrayExt =>
   encode (take (size i1) iK) i1 =
    take (size i1) (encode iK (i1||i2)).
  proof.
    rewrite size_append=> Hlen.
    apply arrayP; split; first by smt.
    move=> k; rewrite /encode size_offun.
    rewrite size_take; first by smt.
    move=> Hk.
    rewrite offunifE // get_take //=; first by smt.
    rewrite offunifE //=; first by smt.
  qed.

  (**
    encode iK.[|i1| .. |i1+i2|] = (encode iK (i1 @ i2)).[|i1| .. |i1+i2|]
  *)
  lemma encode_drop iK i1 i2:
   size iK = size (i1 || i2)%ArrayExt =>
   encode (drop (size i1) iK) i2 =
    drop (size i1) (encode iK (i1||i2)).
  proof.
    rewrite size_append => Hlen.
    apply arrayP; split.
      rewrite size_offun.
      rewrite size_drop; first by smt.
      rewrite size_drop; first by smt.
      by rewrite /encode size_offun; smt.
    move=> k; rewrite /encode size_offun.
    rewrite size_drop; first by smt.
    move=> Hk.
    rewrite offunifE /=. 
    rewrite get_drop //=; first 2 by smt.
    rewrite get_drop /=; first 2 by smt.
    rewrite offunifE //=; first by smt.
  qed.

  (**
    encode iK (i1 @ i2) = (encode ik.[0 .. |i1|] i1) @ (encode ik.[|i1| .. |i1+i2|] i2)
  *)
  lemma encode_take_drop iK i1 i2:
   size iK = size (i1||i2)%ArrayExt =>
   (encode iK (i1 || i2)%Array) =
   ((encode (take (size i1) iK) i1)||(encode (drop (size i1) iK) i2)).
  proof.
    move=> H.
    rewrite -{1}(take_drop iK (size i1)).
      by split; smt.
    rewrite encode_cat //.
      by rewrite size_take; smt.
    by rewrite size_drop; smt.
  qed.
end ProjScheme.
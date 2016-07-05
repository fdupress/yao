(** Extensions to the EasyCrypt Word theory *)

require import Int.
require import IntDiv.
require import FSet.

(** Word type *)
type word.

(** Refinement: we are only interested in words with size >= 2 *)
const length:int.
axiom leq2_length: 2 <= length.

(** 0-word and 1-word *)
op zeros: word.
op ones: word.

(** Last significant bit of a word *)
op getlsb : word -> bool.
op setlsb : word -> bool -> word.

(** Functionality of getlsb and setlsb operations *)
axiom set_getlsb : forall w, setlsb w (getlsb w) = w.
axiom get_setlsb : forall b w, getlsb (setlsb w b) = b.
axiom set_setlsb : forall b c w, setlsb (setlsb w b) c = setlsb w c.

(** Xor operation *)
op ( ^ ): word -> word -> word.

(** Xor properties *)
axiom xorwA (w1 w2 w3:word):
  w1 ^ (w2 ^ w3) = (w1 ^ w2) ^ w3.
axiom xorwC (w1 w2:word):
  w1 ^ w2 = w2 ^ w1.
axiom xorw0 (w:word):
  w ^ zeros = w.
axiom xorwK (w:word):
  w ^ w = zeros.

(** Conversion with bit strings *)
require export ABitstring.

(** Cast to and from bitstring *)
op to_bits: word -> bitstring.
op from_bits: bitstring -> word.

(** Behaviour of the conversion *)
axiom length_to_bits w:
  `|to_bits w| = length.
axiom can_from_to w:
  from_bits (to_bits w) = w.
axiom pcan_to_from (b:bitstring):
  `|b| = length =>
  to_bits (from_bits b) = b.

(** Conversion with int *)
op to_int   : word -> int.
op from_int : int -> word.

(** Behaviour of the conversion *)
axiom to_from w: from_int (to_int w) = w.
axiom from_to i: to_int (from_int i) = i %% 2^length.
axiom from_to_bound i: 0 <= i < 2^length => to_int (from_int i) = i.
axiom from_int_inj : Fun.injective from_int.

(** Probability distribution of our refined and extended Word *)
theory Dword.
  require import Distr.
  require import Real.

  (** Distribution *)
  op dword: word distr.

  (** Probability definition *)
  axiom mu_x_def w: mu_x dword w = 1%r/(2^length)%r.

  (** Losslessness *)
  axiom lossless: is_lossless dword.

  (** Distribution support definition *)
  axiom in_supp_def w: in_supp w dword.

  (** Probability of outputting a word that is in a set X *)
  axiom mu_cpMemw X:
    mu dword (FSet.mem X) = (card X)%r / (2^length)%r.

  (** Probability of outputting a word that is not in a set X *)
  require import Dexcepted.
  axiom lossless_restrw X:
    card X < 2^length =>
    is_lossless (dword \ (fun x, mem X x)).

  (** 
    Probability distribution that generates a random word 
    except the last significant bit which is put at x 
  *)
  op dwordLsb : bool -> word distr.
    
  lemma dwordLsbE b p: mu (dwordLsb b) p = 1%r/(2^(length-1))%r.
  proof. admit. qed.

  (*lemma dword1E w: mu dword (pred1 w) = 1%r / (Alphabet.card^n)%r.
  proof. by rewrite dwordE count_uniq_mem 1:enum_uniq // enumP /b2i. qed.

  lemma support_dword w: support dword w.
  proof.
    rewrite /support /in_supp dword1E divr_gt0 //.
    by rewrite lt_fromint; apply/powPos/Alphabet.card_gt0.
  qed.

  lemma dword_ll: mu dword predT = 1%r.
  proof.
    apply/duniform_ll/negP=> zw; move: (enumP witness).
    by rewrite zw.
  qed.

  lemma dword_uf: is_uniform dword.
  proof.
    apply/duniform_uf/negP=> zw; move: (enumP witness).
    by rewrite zw.
  qed.

  lemma dword_fu: support dword = predT.
  proof. by rewrite pred_ext=> x; rewrite support_dword. qed.*)
  
  (** Probability definition *)
  axiom dwordLsb_mu_x (b:bool) (x:word) : mu_x (dwordLsb b) x = if getlsb x = b then 1%r/(2^(length-1))%r else 0%r.

  (** Losslessness *)
  axiom dwordLsb_lossless (b:bool) : is_lossless (dwordLsb b).

  (** If the word is defined in the distribution, the lsb must be the one defined *)
  axiom lsb_dwordLsb (b:bool) (x:word): in_supp x (dwordLsb b) => getlsb x = b.
end Dword.
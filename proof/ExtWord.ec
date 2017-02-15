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

(** Auxiliar. To be moved or removed *)
lemma from_int_inj_fun a b : a <> b => from_int a <> from_int b by []. 

(** Probability distribution of our refined and extended Word *)
theory Dword.
  require import Distr.
  require import Real.

  op dword: word distr.
  axiom mu_x_def w: mu_x dword w = 1%r/(2^length)%r.
  axiom lossless: is_lossless dword.

  axiom in_supp_def w: in_supp w dword.

  axiom mu_cpMemw X:
    mu dword (FSet.mem X) = (card X)%r / (2^length)%r.

  require import Dexcepted.
  axiom lossless_restrw X:
    card X < 2^length =>
    weight (dword \ (fun x, mem X x)) = 1%r.

  (* generate a random word except the last significant bit which is put at x *)
  op dwordLsb : bool -> word distr.

  axiom dwordLsb_mu_x (b:bool) (x:word) : mu_x (dwordLsb b) x = if getlsb x = b then 1%r/(2^(length-1))%r else 0%r.
  axiom dwordLsb_lossless (b:bool) : is_lossless (dwordLsb b).
  axiom lsb_dwordLsb (b:bool) (x:word): in_supp x (dwordLsb b) => getlsb x = b.
end Dword.

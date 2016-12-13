type top_SomeOT_SomeOT_ESn_H_hkey_t = Word.top_Concrete_W_word
type top_SomeOT_SomeOT_ESn_H_dom_t = Prime_field.top_Prime_field_gf_q
type top_SomeOT_SomeOT_ESn_H_codom_t = Word.top_Concrete_W_word
  
let top_SomeOT_SomeOT_ESn_H_hash : top_SomeOT_SomeOT_ESn_H_hkey_t -> top_SomeOT_SomeOT_ESn_H_dom_t -> top_SomeOT_SomeOT_ESn_H_codom_t = fun k x ->
  let sha256 = Cryptokit.Hash.sha256 () in
  sha256#add_string (Cyclic_group_prime.to_string x);
  String.sub (sha256#result) 0 16

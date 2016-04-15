type dom_t0 = Lint.t

type codom_t0 = string

type hkey_t0 = string

let hash : hkey_t0 -> dom_t0 -> codom_t0 = fun k x ->
  let sha256 = Cryptokit.Hash.sha256 () in
  sha256#add_string (Cyclic_group_prime.to_string x);
  String.sub (sha256#result) 0 16

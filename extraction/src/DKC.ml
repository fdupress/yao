type top_Concrete_ES_SomeGarble_DKCSecurity_D_tweak_t = Word.top_Concrete_W_word
type top_Concrete_ES_SomeGarble_DKCSecurity_D_key1_t = Word.top_Concrete_W_word
type top_Concrete_ES_SomeGarble_DKCSecurity_D_key2_t = Word.top_Concrete_W_word
type top_Concrete_ES_SomeGarble_DKCSecurity_D_msg_t = Word.top_Concrete_W_word
type top_Concrete_ES_SomeGarble_DKCSecurity_D_cipher_t = Word.top_Concrete_W_word

let top_Concrete_ES_SomeGarble_DKCSecurity_D_E : top_Concrete_ES_SomeGarble_DKCSecurity_D_tweak_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_key1_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_key2_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_msg_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_cipher_t = fun tk a b x ->
      let r1 = Word.top_Concrete_W_zeros in
      let r2 = Word.top_Concrete_W_zeros in
      let r3 = Word.top_Concrete_W_zeros in
      let ap = a in
      let bp = b in
      ap.[0] <- Char.chr ((Char.code ap.[0]) land 0xfe);
      bp.[0] <- Char.chr ((Char.code bp.[0]) land 0xfe);
      let aes128A = new Cryptokit.Block.aes_encrypt ap in
      let aes128B = new Cryptokit.Block.aes_encrypt bp in
      aes128A#transform tk 0 r1 0;
      aes128B#transform tk 0 r2 0;
      for i = 0 to 15 do
	r3.[i] <- 
          Char.chr ((Char.code r1.[i]) lxor 
                       (Char.code r2.[i]) lxor (Char.code x.[i]))
      done;
      r3

let top_Concrete_ES_SomeGarble_DKCSecurity_D_D : top_Concrete_ES_SomeGarble_DKCSecurity_D_tweak_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_key1_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_key2_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_cipher_t -> top_Concrete_ES_SomeGarble_DKCSecurity_D_msg_t = fun tk a b y ->
      let r1 = Word.top_Concrete_W_zeros in
      let r2 = Word.top_Concrete_W_zeros in
      let r3 = Word.top_Concrete_W_zeros in
      let ap = String.copy a in
      let bp = String.copy b in
      ap.[0] <- Char.chr ((Char.code ap.[0]) land 0xfe);
      bp.[0] <- Char.chr ((Char.code bp.[0]) land 0xfe);
      let aes128A = new Cryptokit.Block.aes_encrypt ap in
      let aes128B = new Cryptokit.Block.aes_encrypt bp in
      aes128A#transform tk 0 r1 0;
      aes128B#transform tk 0 r2 0;
      for i = 0 to 15 do
	r3.[i] <- 
          Char.chr ((Char.code r1.[i]) lxor 
                       (Char.code r2.[i]) lxor (Char.code y.[i]))
      done;
      r3

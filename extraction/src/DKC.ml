type tweak_t = Word.word
type key1_t = Word.word
type key2_t = Word.word
type msg_t = Word.word
type cipher_t = Word.word

let e : tweak_t -> key1_t -> key2_t -> msg_t -> cipher_t = fun tk a b x ->
      let r1 = String.copy Word.zeros in
      let r2 = String.copy Word.zeros in
      let r3 = String.copy Word.zeros in
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
                       (Char.code r2.[i]) lxor (Char.code x.[i]))
      done;
      r3

let d : tweak_t -> key1_t -> key2_t -> cipher_t -> msg_t = fun tk a b y ->
      let r1 = String.copy Word.zeros in
      let r2 = String.copy Word.zeros in
      let r3 = String.copy Word.zeros in
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

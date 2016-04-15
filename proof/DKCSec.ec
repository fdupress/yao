require import Array.
require import FMap.
require import FSet.
require import Bool.
require import Pair.
require import Option.
require import Int.
require import IntDiv.
require import Distr.
require import List.
require import Real.
require import DBool.

require import DKC.
require ExtWord.

require import ArrayExt.

theory DKCSecurity.
  clone import ExtWord as WD.

  clone export DKC as D with
    type tweak_t = word,
    type key1_t = word,
    type key2_t = word,
    type msg_t = word,
    type cipher_t = word.

  const bound : int.
  axiom bound_pos : 1 < bound. 
    
  (* i * j * pos * tweak *)
  type query = int * int * bool * word.
  type answer = word * word * word.

  op bad : answer.

  module type Adv_DKC_t = {
    proc gen_query (lsb:bool) : query array
    proc get_challenge (answers : answer array) : bool
  }.

  module GameDKC(ADV : Adv_DKC_t) = {

    var real : bool
    var k : word
    var ks : word array
    var rs : word array
    var used : word fset
    
    proc initialize(): bool = {
      var lsb : bool;
      var i : int;

      lsb = $DBool.dbool;
      k = $Dword.dwordLsb lsb;
      rs = $Darray.darray Dword.dword bound;
      i = 0;
      while (i < bound) {
        ks.[i] = $Dword.dwordLsb (i %% 2 = 0);
        i = i+1;
      }

      return lsb;
    }

    proc encrypt(q:query) : answer = {
      var aa,bb,xx : word;
      var i,j : int;
      var pos : bool;
      var t : word;
      var ans : answer;

      ans = bad;
      (i,j,pos,t) = q;
      
      if (!(mem used t || j <= i)) {
        used = used `|` fset1 t;

        if (pos) {
          aa = k;
          bb = ks.[i];
        }
        else {
          aa = ks.[i];
          bb = k;
        }

        if (real) {
          xx = ks.[j];
        }
        else {
          xx = rs.[j];
        }
        ans = (ks.[i], ks.[j],E t aa bb xx);
      }

      return ans;
    }

    proc game(b: bool) : bool = {
      var q : query array;
      var a : answer array;
      var i : int;
      var b' : bool;
      var lsb : bool;
      
      a = offun (fun k, bad) bound;
      lsb = initialize();
      q = ADV.gen_query(lsb);
      i = 0;
      while (i < bound) {  
        a.[i] = encrypt(q.[i]);
        i = i + 1;
      }

      b' = ADV.get_challenge(a);

      return (b' = b);
    }

    proc main() : bool = {
      var adv : bool;
      var lsb : bool;
      
      real = $DBool.dbool;
      adv = game(real);
      return adv;
    }
  }.

  (***************************)
  (* Lossnessness properties *)
  (***************************)

  lemma GameDKCinitialize_lossless (A <: Adv_DKC_t) :
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless GameDKC(A).initialize.
  proof.
    move => Agen_query_ll Aget_challenge_ll.
    proc => //.
    while (0 <= i <= bound) (bound - i); progress.
      by auto; progress; expect 4 by smt. 
    by auto; progress; expect 5 by smt. 
  qed.
  
  lemma GameDKCencrypt_lossless (A <: Adv_DKC_t) :
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless GameDKC(A).encrypt.
  proof. by move => Agen_query_ll Aget_challenge_ll; proc => //; auto. qed.

  lemma GameDKCgame_lossless (A <: Adv_DKC_t) :
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless GameDKC(A).game.
  proof.
    move => Agen_query_ll Aget_challenge_ll.
    proc => //.
    call (_ : true) => //.
    while (0 <= i <= bound) (bound - i); progress.
      wp.
      call (_ : true) => //.
        by auto.
    by skip; smt.
    wp; call (_ : true) => //.
    call (_ : true) => //.
      while (0 <= i <= bound) (bound - i); progress.
        by auto; progress; expect 4 by smt.
      by auto; progress; expect 5 by smt. 
    by wp; skip; smt.  
  qed.

  lemma GameDKCmain_lossless (A <: Adv_DKC_t) :
    islossless A.gen_query =>
    islossless A.get_challenge =>
    islossless GameDKC(A).main.
  proof.
    move => Agen_query_ll Aget_challenge_ll.
    proc => //.
    call (_ : true) => //.
      call (_ : true) => //.
      while (0 <= i <= bound) (bound - i); progress.
        wp.
        call (_ : true) => //.
          by auto.
      by skip; smt.
      wp; call (_ : true) => //.
      call (_ : true) => //.
        while (0 <= i <= bound) (bound - i); progress.
          by auto; progress; expect 4 by smt.
        by auto; progress; expect 5 by smt. 
    by wp; skip; smt.
    by auto; smt.
  qed.

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)
  
  lemma GameDKC_xpnd &m (A <: Adv_DKC_t{GameDKC}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    Pr[GameDKC(A).main()  @ &m: res]
    = 1%r/2%r * (Pr[GameDKC(A).game(true)  @ &m: res]
      + Pr[GameDKC(A).game(false)  @ &m: res]).
  proof. admit. qed.

  lemma GameDKC_adv &m (A <: Adv_DKC_t{GameDKC}):
    islossless A.gen_query =>
    islossless A.get_challenge =>
    2%r * Pr[GameDKC(A).main()  @ &m: res] - 1%r
    = Pr[GameDKC(A).game(true)  @ &m: res] 
      - Pr[GameDKC(A).game(false)  @ &m: !res].
    proof. admit. qed.

end DKCSecurity.
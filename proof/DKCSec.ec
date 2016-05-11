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
  type query_DKC = int * int * bool * word.
  type answer_DKC = word * word * word.

  op bad : answer_DKC.

  module type Adv_DKC_t = {
    proc garble(lsb:bool) : bool
  }.

  module DKCp = {
    var b : bool
    var k : word
    var rr : word array
    var kk : word array
    var used : word fset
  }.

  module type DKC_t = {
    proc initialize() : bool
    proc encrypt(q : query_DKC) : answer_DKC
    proc get_challenge() : bool
  }.
  
  module DKC : DKC_t = {
    
    proc initialize(): bool = {
      var lsb : bool;
      var i : int;

      lsb = ${0,1};
      DKCp.k = $Dword.dwordLsb lsb;
      DKCp.rr = $Darray.darray Dword.dword bound;
      i = 1;
      while (i < bound) {
        DKCp.kk.[i] = $Dword.dwordLsb (i %% 2 = 0);
        i = i+1;
      }

      DKCp.used = FSet.fset0;
      
      return lsb;
    }

    proc get_challenge() : bool = {
      return DKCp.b;
    }
    
    proc encrypt(q:query_DKC) : answer_DKC = {
      var aa,bb,xx : word;
      var i,j : int;
      var pos : bool;
      var t : word;
      var ans : answer_DKC;
      var b : bool;
      
      ans = bad;
      (i,j,pos,t) = q;
      b = get_challenge();
      
      if (!(mem DKCp.used t || j < i)) {
        DKCp.used = DKCp.used `|` fset1 t;

        (aa,bb) = if pos then (DKCp.k, DKCp.kk.[i]) else (DKCp.kk.[i], DKCp.k);
        xx = if b then DKCp.kk.[j] else DKCp.rr.[j];
        
        ans = (DKCp.kk.[i], DKCp.kk.[j], E t aa bb xx);
      }

      return ans;
    }
  }.

(*  module type Batch_t = {
    proc encrypt(qs:query array): answer array
  }.

  module BatchDKC (D:DKC_t): Batch_t = {
    proc encrypt(qs:query array): answer array = {
      var i, n:int;
      var answers:answer array;

      i = 0;
      n = size qs;
      answers = Array.offun (fun x, bad) n;
      while (i < n)
      {
        answers.[i] = D.encrypt(qs.[i]);
        i = i + 1;
      }

      return answers;
    }
  }.*)

  module Game(D:DKC_t, A:Adv_DKC_t) = {
    (*module B = BatchDKC(D)*)

    proc game(b : bool) : bool = {
      var query : query_DKC;
      var answer : answer_DKC;
      var lsb : bool;
      var b' : bool;

      lsb = D.initialize();
      b' = A.garble(lsb);
      return b' = b;
    }

    proc main() : bool = {
      var adv : bool;
      DKCp.b = ${0,1}; 
      adv = game(DKCp.b);
      return adv;
    }
  }.
  
  (***************************)
  (* Lossnessness properties *)
  (***************************)

  (*********************************)
  (* GENERIC ADVANTAGE DEFINITIONS *)
  (*********************************)

end DKCSecurity.
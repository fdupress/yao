(*** A formalization of pseudo-random functions adapted from
EC base theories. **)
require import Option Int Real Distr FSet NewFMap.

theory PRF.

(** A PRF is a family of functions F from domain D to finite range R
    indexed by a keyspace K equipped with a distribution dK. *)
type D.
type R.
type K.

op dK: K distr.
axiom dK_ll: mu dK predT = 1%r.

module type PRF = {
  proc keygen(): K
  proc f(_: K * D): R
}.

module type PRF_Oracles = {
  proc init(): unit
  proc f(_: D): R
}.

module type PRF_Oracle = {
  proc f(_: D): R
}.

module type PRF_Distinguisher(F:PRF_Oracle) = {
  proc distinguish(l : int): bool
}.

module IND (F:PRF_Oracles,D:PRF_Distinguisher) = {
  proc main(l : int): bool = {
    var b;

    F.init();
    b <@ D(F).distinguish(l);
    return b;
  }
}.

op dR: R distr.
axiom dR_ll: mu dR predT = 1%r.

module RandomFunction = {
  var m : (D,R) fmap

  proc init(): unit = {
    m  <- map0;
  }

  proc f(x:D): R = {
    if (!mem (dom m) x) {
      m.[x]  <$ dR;
    }
    return (oget m.[x]);
  }
}.

op F : K -> D -> R.

module PRFr : PRF = {
  proc keygen(): K = {
    var k;

    k <$ dK;
    return k;
  }

  proc f(k:K, x:D) : R = { return F k x; }
}.

module PRFr_Wrapped = {
  var k:K
  proc init(): unit = { k <$ dK; }
  proc f(x:D): R = { return F k x; }
}.

end PRF.
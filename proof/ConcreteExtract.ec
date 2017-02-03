(* -------------------------------------------------------------------- *)
require import Real Int Pair Array.
require (*--*) Concrete.

extraction "SFE.ml_tmp" 
  op p1_stage1,
  op p1_stage2,
  op p2_stage1,
  op p2_stage2
with
  theory Array = "EcIArray",
  theory Prime_field = "Prime_field",
  theory Cyclic_group_prime = "Cyclic_group_prime",
  theory Concrete.W = "Word",
  theory Concrete.ES.DKCScheme.DKCSecurity.D = "DKC",
  theory Concrete.SomeOT.ESn.H = "Hash".

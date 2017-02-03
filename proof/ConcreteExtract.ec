(* -------------------------------------------------------------------- *)
require import Real Int Pair Array.
require (*--*) Concrete.

import Concrete.

print Concrete.
print ArrayExt.

extraction "SFE.ml_tmp" 
  op Concrete.p1_stage1,
  op Concrete.p1_stage2,
  op Concrete.p2_stage1,
  op Concrete.p2_stage2
with
  theory Array = "EcIArray",
  theory Prime_field = "Prime_field",
  theory Cyclic_group_prime = "Cyclic_group_prime",
  theory Concrete.W = "Word",
  theory Concrete.ES.SomeGarble.SomeDKC = "DKC",
  theory Concrete.SomeOT.ESn.H = "Hash".

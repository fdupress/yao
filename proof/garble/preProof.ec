require import Int.

require Dkc.
require GarbledCircuit.
require INDCPA.

(* Security parameter and bound on circuit size*)
theory Cst.
op k : int.
axiom kVal : k > 1.

op bound : int.
axiom boundInf : bound > 1.
end Cst.

(* Take a semi concrete DKC *)
clone Dkc.DKC as DKC with
  op k = Cst.k
  proof kVal by apply Cst.kVal.

(* Definition of security of DKC *)
clone Dkc.DKC_Sec as DKCS with
  theory DKC_Abs = DKC.

(* Take a GarbleCircuit *)
clone export GarbledCircuit as GC with
  theory Cst = Cst,
  theory DKC = DKC.

(* We want to prove PrvInd security base on INDCPA *)
clone Garble.PrvInd as PrvInd_Circuit with
  theory Garble = GC.GarbleCircuit.
clone INDCPA.INDCPA_Def as PrvIndSec with
  theory INDCPA_Scheme = PrvInd_Circuit.INDCPA_Scheme.
require import Int.

require Dkc.
require GarbledCircuit.

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

(* Generate GarbleCircuit *)
clone export GarbledCircuit as GC with
  theory Cst = Cst,
  theory DKC = DKC.
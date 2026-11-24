import BeatAvg.K8.Final

/-! Statement and axioms of the proof of `C = B*` with no `native_decide` (see `repro/KERNEL.md`). -/

open BeatAvg
#check @K8.C_eq_Bstar_kernel
#print axioms K8.C_eq_Bstar_kernel
#check @K8.C_le_Bstar_kernel
#print axioms K8.C_le_Bstar_kernel

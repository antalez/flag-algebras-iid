import BeatAvg.Cert.Order8

/-!
# Order 8 with the finite check of `Cert/Native8.lean`
-/

namespace BeatAvg

/-- **Order 8.** `C ≤ B*`, from the finite check alone. -/
theorem C_le_Bstar_of_main8 : C ≤ Bstar :=
  C_le_Bstar_of_check main8

end BeatAvg

import Fast.Cert7

/-!
# The finite check of the order-7 certificate, by `native_decide`
-/

namespace BeatAvg

/-- All 136,800 seven-point patterns satisfy the certificate inequality. -/
theorem check7_ok : Fast.check7 () = true := by native_decide

end BeatAvg

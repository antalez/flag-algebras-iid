import Fast.Check8

/-!
# The finite check of the order-8 certificate, by `native_decide`

This module imports only the compiled library `Fast`, so that it is rebuilt only when `Fast`
changes.
-/

namespace BeatAvg

/-- All 45,319,744 leaves of the level-8 enumeration pass (about 90 minutes on 192 threads). -/
theorem main8 : Fast.check8 () = true := by native_decide

end BeatAvg

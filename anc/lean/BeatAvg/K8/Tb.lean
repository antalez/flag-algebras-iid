import BeatAvg.K8.EvalF
import BeatAvg.K8.Tables
import BeatAvg.K8.TablesQ

/-!
# The tables of the kernel evaluation
-/

namespace BeatAvg.K8.D

/-- The tables of the order-8 certificate. -/
def tb : Tb := ⟨sub5, sq, deg, thr, obj, ftP, ctP, QT, wQ, offQ, DT, wD, offD, TT, wT, offT,
  Dn, encLo, encHi, encM⟩

end BeatAvg.K8.D

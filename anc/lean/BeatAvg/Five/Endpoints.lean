import BeatAvg.Five.Field
import Fast.Five.Checked

/-! Real endpoint bounds for each of the 307 retained patterns.
These finite statements feed into the equality theorem in Final.lean. -/
namespace BeatAvg.Five
open Fast.Five

theorem retained_endpoint_bounds (p : Pattern) (hp : p ∈ Data.patterns.toList) :
    evalK (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.bstar) ≤ Bstar ∧
    evalK (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.one) ≤ 1 - 9/10000 := by
  exact endpoint_sound ((List.all_eq_true.mp Checked.endpoints) p hp)

end BeatAvg.Five

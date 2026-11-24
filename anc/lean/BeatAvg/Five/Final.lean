import BeatAvg.Five.FinalCore
import Fast.Five.AssemblyChecked
import BeatAvg.Lower.Main

/-! Equality from the five-point colored certificate. All finite computations
are proved by the Lean kernel, and the lower construction is reused unchanged. -/
namespace BeatAvg.Five
open Fast.Five

theorem C_le_Bstar : C ≤ Bstar :=
  C_le_Bstar_of_assembly (fun p hp => (List.all_eq_true.mp AssemblyChecked.all) p hp)

theorem C_eq_Bstar : C = Bstar := le_antisymm C_le_Bstar BeatAvg.Bstar_le_C

end BeatAvg.Five

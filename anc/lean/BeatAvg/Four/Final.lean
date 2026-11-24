import BeatAvg.Four.Evaluation
import BeatAvg.Lower.Main

/-! Direct four-point equality, with kernel-only finite checks. -/
namespace BeatAvg.Four
open Fast.Four Function

theorem sample_bound (v : Fin 4 → ℝ) (hv : Generic v) : Lam v ≤ Bstar := by
  let σ := Tuple.sort v
  have hs : Generic (v ∘ σ) := hv.comp_perm σ
  have hm : Monotone (v ∘ σ) := Tuple.monotone_sort v
  obtain ⟨p, hp, hbits⟩ := sorted_sample_covered hs hm
  have hc : Data.endpointOk p = true :=
    (List.all_eq_true.mp Checked.endpoints) p hp
  rw [← Lam_comp_perm v σ, Lam_eval hs hm hbits]
  exact endpoint_sound hc

theorem C_le_Bstar : C ≤ Bstar := C_le_of_samples Bstar sample_bound

theorem C_eq_Bstar : C = Bstar := le_antisymm C_le_Bstar BeatAvg.Bstar_le_C

end BeatAvg.Four

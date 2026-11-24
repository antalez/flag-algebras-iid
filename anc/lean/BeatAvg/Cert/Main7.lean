import BeatAvg.Cert.Order7b
import BeatAvg.Cert.Order8
import BeatAvg.Cert.Native7

/-!
# The order-7 bound `C ≤ 0.4007545`, with the finite check of `Cert/Native7.lean`
-/

open Function

namespace BeatAvg

/-- **Order 7.** `C ≤ 0.4007545`. -/
theorem C_le_order7 : C ≤ 801509 / 2000000 := by
  have hall : ∀ P ∈ Fast.R7.toList, Fast.eval7 Fast.cert7 P = true := by
    have h := check7_ok
    unfold Fast.check7 at h
    rw [List.all_eq_true] at h
    intro P hP
    exact h _ (List.mem_map_of_mem hP)
  exact flag_bound Fast.e47 e47_inj (fams7 Fast.cert7) (fams7_good Fast.cert7) _
    (LamF_le_of_sorted _ _ _ fun ω hω =>
      eval7_sound Fast.cert7 hω (hall _ (R7_complete (SG_extNn (by norm_num) hω))))

end BeatAvg

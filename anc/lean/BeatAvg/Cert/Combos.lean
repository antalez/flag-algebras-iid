import BeatAvg.Cert.PatReal

/-!
# The list of quadruples and the entries of a pattern
-/

namespace BeatAvg

theorem combos_getD {n i : ℕ} (hi : i < (Fast.combos n).length) :
    (Fast.combos n).getD i (0, 0, 0, 0) ∈ Fast.combos n := by
  have : (Fast.combos n).getD i (0, 0, 0, 0) = (Fast.combos n)[i] := by simp [List.getD, hi]
  rw [this]
  exact List.getElem_mem hi

theorem patArr_getD (n : ℕ) (w : ℕ → ℝ) {i : ℕ} (hi : i < (Fast.combos n).length) :
    (patArr n w).getD i 0 = trit w ((Fast.combos n).getD i (0, 0, 0, 0)) := by
  unfold patArr
  simp [Array.getD, List.getD, hi]

theorem patArr_size (n : ℕ) (w : ℕ → ℝ) : (patArr n w).size = (Fast.combos n).length := by
  simp [patArr]

end BeatAvg

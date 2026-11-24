import BeatAvg.Sample
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The quadratic-form hypothesis follows from Mathlib's `Matrix.PosSemidef`
-/

namespace BeatAvg

theorem quadForm_nonneg_of_posSemidef {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (h : Q.PosSemidef)
    (v : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, v i * Q i j * v j := by
  have h1 := h.dotProduct_mulVec_nonneg v
  have h2 : star v ⬝ᵥ (Q.mulVec v) = ∑ i, ∑ j, v i * Q i j * v j := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h2] at h1
  exact h1

end BeatAvg

import Mathlib.Tactic

/-! The separating-combination argument behind excluded pattern prefixes. -/
namespace BeatAvg.Five
open Finset

/-- A positive combination of strictly negative forms cannot have nonnegative
coefficients on nonnegative gaps. This also allows the first gap to be zero. -/
theorem gordan_exclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → κ → ℝ) (w : ι → ℝ) (x : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwpos : ∃ i, 0 < w i)
    (hx : ∀ j, 0 ≤ x j)
    (hform : ∀ i, ∑ j, a i j * x j < 0)
    (hcoef : ∀ j, 0 ≤ ∑ i, w i * a i j) : False := by
  classical
  have hneg : ∑ i, w i * (∑ j, a i j * x j) < 0 := by
    apply sum_neg'
    · intro i _
      exact mul_nonpos_of_nonneg_of_nonpos (hw i) (hform i).le
    · obtain ⟨i, hi⟩ := hwpos
      exact ⟨i, mem_univ _, mul_neg_of_pos_of_neg hi (hform i)⟩
  have hid : ∑ i, w i * (∑ j, a i j * x j) =
      ∑ j, (∑ i, w i * a i j) * x j := by
    simp only [mul_sum, sum_mul, mul_assoc]
    exact sum_comm
  have hnonneg : 0 ≤ ∑ j, (∑ i, w i * a i j) * x j :=
    sum_nonneg fun j _ => mul_nonneg (hcoef j) (hx j)
  rw [hid] at hneg
  exact (not_lt_of_ge hnonneg) hneg

end BeatAvg.Five

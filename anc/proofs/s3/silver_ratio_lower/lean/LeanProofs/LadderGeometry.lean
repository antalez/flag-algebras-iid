module
public import Mathlib
set_option linter.style.header false
@[expose] public section
noncomputable section

namespace Endpoint

def kappa : ℝ := 1 + Real.sqrt 2
def rung (j : ℕ) : ℝ := Real.sqrt 2 - (Real.sqrt 2 - 1) * (1 / 4 : ℝ) ^ j

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
theorem sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  have := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [sqrt_two_sq]
theorem sqrt_two_lt_three_halves : Real.sqrt 2 < (3 / 2 : ℝ) := by
  have := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [sqrt_two_sq]
theorem kappa_pos : 0 < kappa := by unfold kappa; positivity
theorem kappa_gt_two : 2 < kappa := by unfold kappa; linarith [sqrt_two_gt_one]

@[simp] theorem rung_zero : rung 0 = 1 := by unfold rung; simp

theorem rung_lt_sqrt (j : ℕ) : rung j < Real.sqrt 2 := by
  unfold rung
  have : 0 < (Real.sqrt 2 - 1) * (1 / 4 : ℝ) ^ j :=
    mul_pos (by linarith [sqrt_two_gt_one]) (pow_pos (by norm_num) _)
  linarith

theorem rung_strictMono : StrictMono rung := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold rung
  rw [pow_succ]
  have : 0 < (Real.sqrt 2 - 1) * (1 / 4 : ℝ) ^ j :=
    mul_pos (by linarith [sqrt_two_gt_one]) (pow_pos (by norm_num) _)
  nlinarith

theorem one_le_rung (j : ℕ) : 1 ≤ rung j := by
  simpa using rung_strictMono.monotone (Nat.zero_le j)

theorem rung_nonneg (j : ℕ) : 0 ≤ rung j := le_trans (by norm_num) (one_le_rung j)

theorem rung_step (j : ℕ) : 2 + rung j < kappa * rung (j + 1) := by
  have hs := sqrt_two_sq
  have h1 := sqrt_two_gt_one
  have h2 := sqrt_two_lt_three_halves
  have ht : 0 < (1 / 4 : ℝ) ^ j := pow_pos (by norm_num) _
  unfold rung kappa
  rw [pow_succ]
  nlinarith [mul_pos ht (show 0 < 4 * Real.sqrt 2 - 5 by nlinarith)]

theorem rung_skip {j k : ℕ} (h : j < k) : 2 + rung j < kappa * rung k := by
  exact lt_of_lt_of_le (rung_step j)
    (mul_le_mul_of_nonneg_left (rung_strictMono.monotone h) (le_of_lt kappa_pos))

theorem three_lt_target (j : ℕ) : 3 < kappa * rung (j + 1) := by
  have := rung_skip (show 0 < j + 1 by omega)
  norm_num only [rung_zero] at this
  exact this

end Endpoint

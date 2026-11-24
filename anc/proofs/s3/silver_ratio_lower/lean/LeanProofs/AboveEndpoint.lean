module
public import LeanProofs.Amplification
public import LeanProofs.LadderGeometry
set_option linter.style.header false
@[expose] public section
noncomputable section
open scoped BigOperators Classical
namespace Endpoint
namespace AboveEndpoint

def x : Fin 3 → ℝ := ![0, Real.sqrt 2 / 2, 1]
def w : Fin 3 → ℝ := ![1 / 3, 1 / 2, 1 / 6]

def base : Law (Fin 3) where
  x := x
  w := w
  x_nonneg i := by
    fin_cases i
    · norm_num [x]
    · change 0 ≤ Real.sqrt 2 / 2
      positivity
    · norm_num [x]
  w_nonneg i := by fin_cases i <;> norm_num [w]
  total := by norm_num [w, Fin.sum_univ_succ]

def count (t a b d : Fin 3) : ℕ :=
  (if a = t then 1 else 0) + (if b = t then 1 else 0) + (if d = t then 1 else 0)

abbrev good (a b d t : Fin 3) : Prop :=
  if t = 0 then False else
  if t = 1 then count 2 a b d ≤ 1 ∧ count 1 a b d ≤ 2 ∧
    (count 2 a b d = 0 ∨ count 1 a b d ≤ 1)
  else count 2 a b d ≤ 1 ∨ (count 2 a b d = 2 ∧ count 1 a b d = 0)

theorem good_wins (c : ℝ) (hc : kappa < c) (a b d t : Fin 3)
    (h : good a b d t) : x a + x b + x d < c * x t := by
  have h1 := sqrt_two_gt_one
  have h2 := sqrt_two_lt_three_halves
  have hs := sqrt_two_sq
  unfold kappa at hc
  have ha : (1 + Real.sqrt 2) * (Real.sqrt 2 / 2) < c * (Real.sqrt 2 / 2) :=
    mul_lt_mul_of_pos_right hc (by positivity)
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases t <;>
    norm_num [good, count] at h <;> norm_num [x] <;> nlinarith

theorem base_lower (c : ℝ) (hc : kappa < c) : (161 / 324 : ℝ) ≤ base.prob c := by
  have ha := base.accepted_le c
    (fun a : Quad (Fin 3) => good a.1 a.2.1 a.2.2.1 a.2.2.2)
    (fun a h => good_wins c hc _ _ _ _ h)
  have hcount : (∑ a : Quad (Fin 3),
      if good a.1 a.2.1 a.2.2.1 a.2.2.2 then base.weight a else 0) = (161 / 324 : ℝ) := by
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, good, count, Law.weight, base, w]
  rwa [hcount] at ha

/-- One zero replacement is enough. Although the labels are 3×3, the locations
are exactly among 0, e*sqrt(2)/2, e, sqrt(2)/2, 1. -/
theorem exists_jump_scale (c : ℝ) (hc : kappa < c) :
    ∃ e : ℝ, ∃ he : 0 < e,
      (6601 / 13122 : ℝ) ≤ (base.addScaled base e he.le).prob c := by
  obtain ⟨e, he, hQ⟩ := base.exists_amplification_scale base c 0 (by simp [base, x])
  let Q := base.addScaled base e he.le
  have hb := base_lower c hc
  refine ⟨e, he, ?_⟩
  norm_num [base, w] at hQ
  change base.prob c + (1 / 81 : ℝ) * base.prob c ≤ Q.prob c at hQ
  linarith

theorem exists_jump (c : ℝ) (hc : kappa < c) :
    ∃ Q : Law (Fin 3 × Fin 3), (6601 / 13122 : ℝ) ≤ Q.prob c := by
  obtain ⟨e, he, h⟩ := exists_jump_scale c hc
  exact ⟨base.addScaled base e he.le, h⟩

theorem exists_probability_gt_half (c : ℝ) (hc : 1 + Real.sqrt 2 < c) :
    ∃ Q : Law (Fin 3 × Fin 3), 1 / 2 < Q.prob c := by
  obtain ⟨Q, hQ⟩ := exists_jump c hc
  exact ⟨Q, lt_of_lt_of_le (by norm_num) hQ⟩

end AboveEndpoint
end Endpoint

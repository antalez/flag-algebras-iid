import BeatAvg.Four.SamplePattern

namespace BeatAvg.Four
open Fast.Four

theorem bit0_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 0 = decide (v 1 < cut 0 * v 0) := by
  rw [hb 0 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit1_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 1 = decide (v 1 < cut 1 * v 0) := by
  rw [hb 1 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit2_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 2 = decide (v 1 < cut 2 * v 0) := by
  rw [hb 2 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit3_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 3 = decide (v 2 < cut 0 * v 0) := by
  rw [hb 3 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit4_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 4 = decide (v 2 < cut 1 * v 0) := by
  rw [hb 4 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit5_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 5 = decide (v 2 < cut 2 * v 0) := by
  rw [hb 5 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit6_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 6 = decide (v 3 < cut 0 * v 0) := by
  rw [hb 6 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit7_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 7 = decide (v 3 < cut 1 * v 0) := by
  rw [hb 7 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit8_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 8 = decide (v 3 < cut 2 * v 0) := by
  rw [hb 8 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit9_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 9 = decide (v 2 < cut 0 * v 1) := by
  rw [hb 9 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit10_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 10 = decide (v 2 < cut 1 * v 1) := by
  rw [hb 10 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit11_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 11 = decide (v 2 < cut 2 * v 1) := by
  rw [hb 11 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit12_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 12 = decide (v 3 < cut 0 * v 1) := by
  rw [hb 12 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit13_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 13 = decide (v 3 < cut 1 * v 1) := by
  rw [hb 13 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit14_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 14 = decide (v 3 < cut 2 * v 1) := by
  rw [hb 14 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit15_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 15 = decide (v 3 < cut 0 * v 2) := by
  rw [hb 15 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit16_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 16 = decide (v 3 < cut 1 * v 2) := by
  rw [hb 16 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit17_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 17 = decide (v 3 < cut 2 * v 2) := by
  rw [hb 17 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit18_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 18 = decide (v 0+v 1+v 2 < 2*v 3) := by
  rw [hb 18 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

theorem bit19_spec {p : Pattern} {v : Fin 4 → ℝ}
    (hb : ∀ i < 20, p.testBit i = decide (linearValue i v < 0)) :
    p.testBit 19 = decide (v 0+v 1+v 3 < 2*v 2) := by
  rw [hb 19 (by decide)]
  apply decide_eq_decide.mpr
  norm_num [linearValue, form, pairs, cut, cutNum, cutDen, Fast.Five.pairs,
    List.range_succ, Fin.sum_univ_succ]
  all_goals (constructor <;> intro h <;> linarith)

end BeatAvg.Four

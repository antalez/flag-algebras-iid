import BeatAvg.Five.Functional
import BeatAvg.Five.PatternConfig

namespace BeatAvg.Five
open Fast.Five

theorem half_below_iff {v : Fin 5 → ℝ} (hv : Generic v) {i j : Fin 5} (hij : i ≠ j) :
    ((configOf v).additive.lt i j && !(configOf v).close i j) = true ↔ v i < v j / 2 := by
  have ht := hv.2.2.2 j i hij.symm
  by_cases h : v i < v j
  · simp only [configOf, cfgOf, ne_eq, hij, not_false_eq_true, true_and, decide_eq_true_eq, Bool.and_eq_true,
      Bool.not_eq_true, decide_eq_false_iff_not, h, true_and, max_eq_right h.le, min_eq_left h.le]
    simp only [not_decide_eq_true, not_lt]
    constructor
    · intro hh
      have hs : 2*v i < v j := lt_of_le_of_ne hh ht.symm
      linarith
    · intro hh; linarith
  · simp only [configOf, cfgOf, h, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
    linarith [hv.1 j]

theorem twice_below_iff {v : Fin 5 → ℝ} (hv : Generic v) {i j : Fin 5} (hij : i ≠ j) :
    ((configOf v).additive.lt i j || (configOf v).close i j) = true ↔ v i < 2*v j := by
  by_cases h : v i < v j
  · simp only [configOf, cfgOf, h, decide_true, Bool.true_or, true_iff]
    linarith [hv.1 j]
  · have hle : v j ≤ v i := le_of_not_gt h
    simp only [configOf, cfgOf, ne_eq, hij, not_false_eq_true, true_and, h, decide_false, Bool.false_or, decide_eq_true_eq, max_eq_left hle, min_eq_right hle]

theorem class_eq {v : Fin 5 → ℝ} {i j : Fin 5} (hij : i ≠ j) :
    pairClass (v i,v j) =
      (if (configOf v).close i j then 2 else 0) +
      (if (configOf v).additive.lt i j then 0 else 1) := by
  by_cases h : v i < v j
  · simp only [pairClass, configOf, cfgOf, ne_eq, hij, not_false_eq_true, true_and, h, decide_true, ite_true, decide_eq_true_eq, max_eq_right h.le, min_eq_left h.le, add_zero]
  · have hle : v j ≤ v i := le_of_not_gt h
    simp only [pairClass, configOf, cfgOf, ne_eq, hij, not_false_eq_true, true_and, h, decide_false, Bool.false_eq_true,
      ite_false, max_eq_left hle, min_eq_right hle]
    by_cases hh : v i < 2*v j <;> simp [ne_eq, hij, hh]

end BeatAvg.Five

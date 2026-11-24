import BeatAvg.Four.Cover
import BeatAvg.Four.Generic

namespace BeatAvg.Four
open Fast.Four
set_option maxHeartbeats 0

noncomputable def gaps (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![v 0, v 1-v 0, v 2-v 1, v 3-v 2]

noncomputable def linearValue (i : ℕ) (v : Fin 4 → ℝ) : ℝ :=
  ∑ j : Fin 4, (((form i).getD j.val 0 : ℤ) : ℝ)*v j

theorem gaps_nonneg {v : Fin 4 → ℝ} (hv : Generic v) (hm : Monotone v) :
    ∀ j, 0 ≤ gaps v j := by
  intro j
  fin_cases j
  · exact hv.1.1 0
  · exact sub_nonneg.mpr (hm (show (0 : Fin 4) ≤ 1 by decide))
  · exact sub_nonneg.mpr (hm (show (1 : Fin 4) ≤ 2 by decide))
  · exact sub_nonneg.mpr (hm (show (2 : Fin 4) ≤ 3 by decide))

theorem gapValue_gaps (i : Fin 20) (v : Fin 4 → ℝ) :
    gapValue i.val (gaps v) = linearValue i.val v := by
  fin_cases i <;>
    norm_num [gapValue, gaps, linearValue, gapForm, form, pairs, cutNum, cutDen,
      Fast.Five.pairs, List.range_succ, Fin.sum_univ_succ] <;> ring

theorem linearValue_ne_zero {v : Fin 4 → ℝ} (hv : Generic v) (i : Fin 20) :
    linearValue i.val v ≠ 0 := by
  fin_cases i
  · intro h
    have ht := hv.2 0 1 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 1 1 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 2 1 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 0 2 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 1 2 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 2 2 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 0 3 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 1 3 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 2 3 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 0 2 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 1 2 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 2 2 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 0 3 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 1 3 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 2 3 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 0 3 2 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 1 3 2 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.2 2 3 2 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, cutNum, cutDen, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    norm_num [cut, cutNum, cutDen]
    linarith
  · intro h
    have ht := hv.1.2.2 0 1 2 3 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.1.2.2 0 1 3 2 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, Fast.Five.pairs,
      List.range_succ, Fin.sum_univ_succ] at h
    linarith

theorem sorted_sample_covered {v : Fin 4 → ℝ} (hv : Generic v) (hm : Monotone v) :
    ∃ p ∈ Data.patterns.toList,
      ∀ i < 20, p.testBit i = decide (linearValue i v < 0) := by
  classical
  have hn : ∀ i < 20, gapValue i (gaps v) ≠ 0 := by
    intro i hi
    rw [gapValue_gaps ⟨i,hi⟩]
    exact linearValue_ne_zero hv ⟨i,hi⟩
  obtain ⟨p,hp,hfeas,hbits⟩ := exists_feasible (gaps v) (gaps_nonneg hv hm) hn
  refine ⟨p, feasible_retained hp hfeas, ?_⟩
  intro i hi
  rw [hbits i hi, gapValue_gaps ⟨i,hi⟩]

end BeatAvg.Four

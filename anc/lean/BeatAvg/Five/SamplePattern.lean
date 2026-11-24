import BeatAvg.Five.Cover
import BeatAvg.Five.Generic
import BeatAvg.Five.Endpoints

/-! Every sorted real sample in general position is covered by a retained pattern. -/
namespace BeatAvg.Five
open Fast.Five

noncomputable def gaps (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![v 0, v 1-v 0, v 2-v 1, v 3-v 2, v 4-v 3]

noncomputable def linearValue (i : ℕ) (v : Fin 5 → ℝ) : ℝ :=
  ∑ j : Fin 5, (((form i).getD j.val 0 : ℤ) : ℝ)*v j

theorem gaps_nonneg {v : Fin 5 → ℝ} (hv : Generic v) (hm : Monotone v) :
    ∀ j, 0 ≤ gaps v j := by
  intro j
  fin_cases j
  · exact hv.1 0
  · exact sub_nonneg.mpr (hm (show (0 : Fin 5) ≤ 1 by decide))
  · exact sub_nonneg.mpr (hm (show (1 : Fin 5) ≤ 2 by decide))
  · exact sub_nonneg.mpr (hm (show (2 : Fin 5) ≤ 3 by decide))
  · exact sub_nonneg.mpr (hm (show (3 : Fin 5) ≤ 4 by decide))

theorem gapValue_gaps (i : Fin 20) (v : Fin 5 → ℝ) :
    gapValue i.val (gaps v) = linearValue i.val v := by
  fin_cases i <;>
    norm_num [gapValue, gaps, linearValue, gapForm, form, pairs, quads, choose,
      List.range_succ, Fin.sum_univ_succ] <;> ring

theorem linearValue_ne_zero {v : Fin 5 → ℝ} (hv : Generic v) (i : Fin 20) :
    linearValue i.val v ≠ 0 := by
  fin_cases i
  · intro h
    have ht := hv.2.2.2 1 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 2 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 3 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 4 0 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 2 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 3 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 4 1 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 3 2 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 4 2 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.2 4 3 (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 1 3 2 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 1 2 3 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 1 4 2 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 1 2 4 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 1 4 3 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 1 3 4 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 2 4 3 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 0 2 3 4 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 1 2 4 3 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith
  · intro h
    have ht := hv.2.2.1 1 2 3 4 (by decide) (by decide) (by decide)
    apply ht
    norm_num [linearValue, form, pairs, quads, choose, List.range_succ, Fin.sum_univ_succ] at h
    linarith

/-- Coverage and the exact real endpoint bounds for a sorted sample, with the
recorded bits explicitly identified with the twenty defining comparisons. -/
theorem sorted_sample_covered {v : Fin 5 → ℝ} (hv : Generic v) (hm : Monotone v) :
    ∃ p ∈ Data.patterns.toList,
      (∀ i < 20, p.testBit i = decide (linearValue i v < 0)) ∧
      evalK (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.bstar) ≤ Bstar ∧
      evalK (score Data.blocks Data.wHalf Data.wTwice Data.nu p Fast.K.one) ≤ 1-9/10000 := by
  classical
  have hn : ∀ i < 20, gapValue i (gaps v) ≠ 0 := by
    intro i hi
    rw [gapValue_gaps ⟨i,hi⟩]
    exact linearValue_ne_zero hv ⟨i,hi⟩
  obtain ⟨p,hp,hfeas,hbits⟩ := exists_feasible (gaps v) (gaps_nonneg hv hm) hn
  have hret := feasible_retained hp hfeas
  refine ⟨p, hret, ?_, retained_endpoint_bounds p hret⟩
  intro i hi
  rw [hbits i hi, gapValue_gaps ⟨i,hi⟩]

end BeatAvg.Five

import BeatAvg.Four.FlagExpectation
import BeatAvg.Four.Matrix

namespace BeatAvg.Four
open Fast.Four Function MeasureTheory

noncomputable def pairFamily (b : Block) : Fam 4 2 1 where
  eR := fun i => ⟨i.val, by omega⟩
  eT := fun _ => 2
  eT' := fun _ => 3
  F := pairFlag b
  N := b.flags.size+1
  Q := fun i j => evalK (expandedEntry b i j)

theorem pair_injective (b : Block) : Injective (pairFamily b).e := by
  unfold Fam.e pairFamily
  dsimp only
  decide +kernel

noncomputable def familyTerms : Fin 4 → (Fin 4 → ℝ) → ℝ :=
  ![(pairFamily Data.block0).term, (pairFamily Data.block1).term,
    (pairFamily Data.block2).term, (pairFamily Data.block3).term]

theorem familyTerms_bm (i : Fin 4) : BM (familyTerms i) := by
  fin_cases i <;> exact Fam.bm_K _ |>.comp (by fun_prop)

theorem familyTerms_nonneg (i : Fin 4) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ v, familyTerms i v ∂(iid 4 μ) := by
  fin_cases i
  · exact (pairFamily Data.block0).integral_term_nonneg (pair_injective _)
      (fun _ v => block_psd _ Checked.shape0 Checked.psd0 v) μ
  · exact (pairFamily Data.block1).integral_term_nonneg (pair_injective _)
      (fun _ v => block_psd _ Checked.shape1 Checked.psd1 v) μ
  · exact (pairFamily Data.block2).integral_term_nonneg (pair_injective _)
      (fun _ v => block_psd _ Checked.shape2 Checked.psd2 v) μ
  · exact (pairFamily Data.block3).integral_term_nonneg (pair_injective _)
      (fun _ v => block_psd _ Checked.shape3 Checked.psd3 v) μ

end BeatAvg.Four

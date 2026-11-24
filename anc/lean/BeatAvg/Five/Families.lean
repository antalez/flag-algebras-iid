import BeatAvg.Five.FlagExpectation
import BeatAvg.Five.Matrices
import Fast.Five.FlagCodes

/-! The six concrete colored flag families from the certificate. -/
open MeasureTheory Function
namespace BeatAvg.Five
open Fast.Five

noncomputable def singletonFamily (b : Block) : Fam 5 1 2 where
  eR := fun _ => 0
  eT := fun i => ⟨i.val+1, by omega⟩
  eT' := fun i => ⟨i.val+3, by omega⟩
  F := singletonFlag b
  N := b.flags.size+1
  Q := fun i j => evalK (expandedEntry b i j)

noncomputable def tripleFamily (b : Block) : Fam 5 3 1 where
  eR := fun i => ⟨i.val, by omega⟩
  eT := fun _ => 3
  eT' := fun _ => 4
  F := tripleFlag b
  N := b.flags.size+1
  Q := fun i j => evalK (expandedEntry b i j)

theorem singleton_injective (b : Block) : Injective (singletonFamily b).e := by
  unfold Fam.e singletonFamily
  dsimp only
  decide +kernel

theorem triple_injective (b : Block) : Injective (tripleFamily b).e := by
  unfold Fam.e tripleFamily
  dsimp only
  decide +kernel

theorem singleton_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, (singletonFamily Data.block0).term ω ∂(iid 5 μ) :=
  (singletonFamily Data.block0).integral_term_nonneg (singleton_injective _)
    (fun _ v => block0_psd v) μ

theorem triple1_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, (tripleFamily Data.block1).term ω ∂(iid 5 μ) :=
  (tripleFamily Data.block1).integral_term_nonneg (triple_injective _)
    (fun _ v => block1_psd v) μ

theorem triple2_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, (tripleFamily Data.block2).term ω ∂(iid 5 μ) :=
  (tripleFamily Data.block2).integral_term_nonneg (triple_injective _)
    (fun _ v => block2_psd v) μ

theorem triple3_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, (tripleFamily Data.block3).term ω ∂(iid 5 μ) :=
  (tripleFamily Data.block3).integral_term_nonneg (triple_injective _)
    (fun _ v => block3_psd v) μ

theorem triple4_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, (tripleFamily Data.block4).term ω ∂(iid 5 μ) :=
  (tripleFamily Data.block4).integral_term_nonneg (triple_injective _)
    (fun _ v => block4_psd v) μ

theorem triple5_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ ω, (tripleFamily Data.block5).term ω ∂(iid 5 μ) :=
  (tripleFamily Data.block5).integral_term_nonneg (triple_injective _)
    (fun _ v => block5_psd v) μ

end BeatAvg.Five

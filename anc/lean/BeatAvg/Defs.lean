import BeatAvg.PiLemmas
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Beat the Average constant

`C = sup_μ P(X₁ + X₂ + X₃ < 2 X₄)` over laws `μ` on `[0, ∞)`, with `X₁..X₄` iid `μ`.
-/

open MeasureTheory Set Function

namespace BeatAvg

/-- The success event `x₀ + x₁ + x₂ < 2 x₃`. -/
def S4 : Set (Fin 4 → ℝ) := {x | x 0 + x 1 + x 2 < 2 * x 3}

theorem measurableSet_S4 : MeasurableSet S4 :=
  measurableSet_lt (by fun_prop) (by fun_prop)

/-- A law on `[0, ∞)`: a Borel probability measure on `ℝ` giving no mass to the negative reals. -/
structure IsLaw (μ : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  nonneg : μ (Iio 0) = 0

/-- The iid product of `n` copies of `μ`. -/
noncomputable abbrev iid (n : ℕ) (μ : Measure ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => μ

/-- `P(μ) = P(X₁ + X₂ + X₃ < 2 X₄)` for `X₁..X₄` iid `μ`. -/
noncomputable def P (μ : Measure ℝ) : ℝ := (iid 4 μ).real S4

/-- The constant `C = sup_μ P(μ)`. -/
noncomputable def C : ℝ := sSup {p | ∃ μ : Measure ℝ, IsLaw μ ∧ P μ = p}

theorem P_nonneg (μ : Measure ℝ) : 0 ≤ P μ := measureReal_nonneg

theorem P_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] : P μ ≤ 1 := by
  unfold P
  exact measureReal_le_one

theorem bddAbove_P : BddAbove {p | ∃ μ : Measure ℝ, IsLaw μ ∧ P μ = p} := by
  refine ⟨1, ?_⟩
  rintro p ⟨μ, hμ, rfl⟩
  have := hμ.prob
  exact P_le_one μ

theorem P_le_C {μ : Measure ℝ} (hμ : IsLaw μ) : P μ ≤ C :=
  le_csSup bddAbove_P ⟨μ, hμ, rfl⟩

theorem isLaw_dirac : IsLaw (Measure.dirac (1 : ℝ)) :=
  ⟨inferInstance, by simp⟩

theorem nonempty_P : {p | ∃ μ : Measure ℝ, IsLaw μ ∧ P μ = p}.Nonempty :=
  ⟨P (Measure.dirac 1), Measure.dirac 1, isLaw_dirac, rfl⟩

theorem C_nonneg : 0 ≤ C := (P_nonneg _).trans (P_le_C isLaw_dirac)

theorem C_le_one : C ≤ 1 := by
  refine csSup_le nonempty_P ?_
  rintro p ⟨μ, hμ, rfl⟩
  have := hμ.prob
  exact P_le_one μ

/-- Laws whose value is within `ε` of the supremum. -/
theorem exists_law_gt {ε : ℝ} (hε : 0 < ε) : ∃ μ : Measure ℝ, IsLaw μ ∧ C - ε < P μ := by
  have h : C - ε < C := by linarith
  obtain ⟨p, ⟨μ, hμ, rfl⟩, hp⟩ := exists_lt_of_lt_csSup nonempty_P h
  exact ⟨μ, hμ, hp⟩

/-- The iid product gives no mass to samples with a negative coordinate. -/
theorem iid_nonneg_ae {n : ℕ} {μ : Measure ℝ} (hμ : IsLaw μ) :
    ∀ᵐ x ∂(iid n μ), ∀ i, 0 ≤ x i := by
  have := hμ.prob
  rw [ae_all_iff]
  intro i
  have : (iid n μ) {x | x i < 0} = 0 :=
    Measure.pi_eval_preimage_null (fun _ : Fin n => μ) (i := i) hμ.nonneg
  rw [ae_iff]
  simpa using this

/-- Scale invariance. -/
theorem P_map_mul {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) :
    P (μ.map (fun x => c * x)) = P μ := by
  have hm : Measurable (fun x : ℝ => c * x) := by fun_prop
  have : IsProbabilityMeasure (μ.map (fun x => c * x)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  unfold P iid
  rw [← Measure.pi_map_pi (fun _ => hm.aemeasurable),
    map_measureReal_apply (by fun_prop) measurableSet_S4]
  congr 1
  ext x
  simp only [S4, mem_preimage, mem_ofPred_eq]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem isLaw_map_mul {μ : Measure ℝ} (hμ : IsLaw μ) {c : ℝ} (hc : 0 < c) :
    IsLaw (μ.map (fun x => c * x)) := by
  have hm : Measurable (fun x : ℝ => c * x) := by fun_prop
  have := hμ.prob
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, ?_⟩
  rw [Measure.map_apply hm measurableSet_Iio]
  refine measure_mono_null ?_ hμ.nonneg
  intro x hx
  simp only [mem_preimage, mem_Iio] at hx ⊢
  by_contra h
  have := mul_nonneg hc.le (not_lt.mp h)
  linarith

end BeatAvg

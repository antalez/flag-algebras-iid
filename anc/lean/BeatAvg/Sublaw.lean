import BeatAvg.Defs

/-!
# Lemma 2.1 (sub-law)

The successes among four draws that all fall below `b` have probability at most `C F(b)^4`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace BeatAvg

theorem sublaw {μ : Measure ℝ} (hμ : IsLaw μ) (b : ℝ) :
    (iid 4 μ).real (S4 ∩ {x | ∀ i, x i < b}) ≤ C * (μ.real (Iio b)) ^ 4 := by
  have := hμ.prob
  have hbox : {x : Fin 4 → ℝ | ∀ i, x i < b} = univ.pi (fun _ => Iio b) := by
    ext x; simp
  have h1 : (iid 4 μ) (S4 ∩ {x | ∀ i, x i < b})
      = Measure.pi (fun _ : Fin 4 => μ.restrict (Iio b)) S4 := by
    rw [hbox, ← Measure.restrict_pi_pi, Measure.restrict_apply measurableSet_S4]
  by_cases hF0 : μ (Iio b) = 0
  · have h0 : (iid 4 μ) (S4 ∩ {x | ∀ i, x i < b}) = 0 := by
      refine measure_mono_null inter_subset_right ?_
      rw [hbox, Measure.pi_pi]
      simp [hF0]
    simp [Measure.real, h0, hF0]
  · have hFtop : μ (Iio b) ≠ ∞ := measure_ne_top _ _
    obtain ⟨ν, hνdef⟩ : ∃ ν : Measure ℝ, ν = (μ (Iio b))⁻¹ • μ.restrict (Iio b) := ⟨_, rfl⟩
    have hν : IsLaw ν := by
      refine ⟨⟨?_⟩, ?_⟩
      · simp [hνdef, ENNReal.inv_mul_cancel hF0 hFtop]
      · have : (μ.restrict (Iio b)) (Iio 0) = 0 := by
          rw [Measure.restrict_apply measurableSet_Iio]
          exact measure_mono_null inter_subset_left hμ.nonneg
        simp [hνdef, this]
    have hsm : μ.restrict (Iio b) = μ (Iio b) • ν := by
      rw [hνdef, smul_smul, ENNReal.mul_inv_cancel hF0 hFtop, one_smul]
    have := hν.prob
    have h2 : Measure.pi (fun _ : Fin 4 => μ.restrict (Iio b))
        = μ (Iio b) ^ 4 • Measure.pi (fun _ : Fin 4 => ν) := by
      refine Measure.pi_eq fun s hs => ?_
      simp [Measure.smul_apply, Measure.pi_pi, hsm, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ]
    have h3 : (iid 4 μ).real (S4 ∩ {x | ∀ i, x i < b}) = (μ.real (Iio b)) ^ 4 * P ν := by
      simp only [Measure.real, P, iid]
      rw [h1, h2]
      simp [ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [h3]
    have h4 := P_le_C hν
    have h5 : 0 ≤ (μ.real (Iio b)) ^ 4 := by positivity
    nlinarith

end BeatAvg

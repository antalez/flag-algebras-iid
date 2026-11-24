import BeatAvg.Four.Families
import BeatAvg.Four.Generic

/-! The ordinary flag bound, using the existing iid and atomless approximation
lemmas. No restrictions on near-optimal laws are used. -/
namespace BeatAvg.Four
open Fast.Four MeasureTheory Function Finset

noncomputable def squares (v : Fin 4 → ℝ) : ℝ := ∑ i, familyTerms i v
noncomputable def lam (v : Fin 4 → ℝ) : ℝ := ind S4 v + squares v
noncomputable def Lam (v : Fin 4 → ℝ) : ℝ :=
  (1/24 : ℝ) * ∑ π : Equiv.Perm (Fin 4), lam (v ∘ π)

theorem bm_squares : BM squares := BM.sum _ fun i _ => familyTerms_bm i
theorem bm_lam : BM lam := (BM.ind measurableSet_S4).add bm_squares
theorem bm_Lam : BM Lam :=
  (BM.sum _ fun _ _ => bm_lam.comp (by fun_prop)).const_mul _

theorem integral_squares_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ v, squares v ∂(iid 4 μ) := by
  unfold squares
  rw [integral_finsetSum _ (fun i _ => (familyTerms_bm i).integrable _)]
  exact sum_nonneg fun i _ => familyTerms_nonneg i μ

theorem integral_lam_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    P μ ≤ ∫ v, lam v ∂(iid 4 μ) := by
  unfold lam
  rw [integral_add ((BM.ind measurableSet_S4).integrable _) (bm_squares.integrable _),
    integral_ind _ measurableSet_S4]
  exact le_add_of_nonneg_right (integral_squares_nonneg μ)

theorem integral_Lam (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ v, Lam v ∂(iid 4 μ) = ∫ v, lam v ∂(iid 4 μ) := by
  unfold Lam
  rw [integral_const_mul, integral_finsetSum _ (fun π _ =>
    (bm_lam.comp (by fun_prop)).integrable (iid 4 μ))]
  have hh : ∀ π : Equiv.Perm (Fin 4),
      (∫ v, lam (v ∘ π) ∂(iid 4 μ)) = ∫ v, lam v ∂(iid 4 μ) := by
    intro π
    exact integral_comp_mp (measurePreserving_comp_injective μ π π.injective) bm_lam.meas
  simp only [hh, sum_const, card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]
  ring

theorem Lam_comp_perm (v : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    Lam (v ∘ σ) = Lam v := by
  unfold Lam
  congr 1
  have hh := Equiv.sum_comp (Equiv.mulLeft σ)
    (fun π : Equiv.Perm (Fin 4) => lam (v ∘ π))
  rw [← hh]
  rfl

theorem C_le_of_samples (b : ℝ) (hb : ∀ v, Generic v → Lam v ≤ b) : C ≤ b := by
  have key : ∀ μ : Measure ℝ, IsLaw μ → NullSingletonClass μ → P μ ≤ b := by
    intro μ hμ hna
    have := hμ.prob
    have hup : ∫ v, Lam v ∂(iid 4 μ) ≤ b := by
      have h := integral_mono_ae (bm_Lam.integrable _) (integrable_const b)
        ((ae_generic hμ).mono fun v hv => hb v hv)
      simpa using h
    rw [integral_Lam] at hup
    exact (integral_lam_lower μ).trans hup
  by_contra hc
  have hgt : b < C := not_le.mp hc
  obtain ⟨μ, hμ, hna, hP⟩ := exists_atomless_law_gt (ε := C-b) (by linarith)
  have := key μ hμ hna
  linarith

end BeatAvg.Four
